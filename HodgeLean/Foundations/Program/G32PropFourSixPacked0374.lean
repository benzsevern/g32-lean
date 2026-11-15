import HodgeLean.Foundations.Program.G32PropFourSixPacked0367
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0373
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPacked0368
import HodgeLean.Foundations.Program.G32PropFourSixPacked0369
import HodgeLean.Foundations.Program.G32PropFourSixPacked0370
import HodgeLean.Foundations.Program.G32PropFourSixPacked0371
import HodgeLean.Foundations.Program.G32PropFourSixPacked0372
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_096 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 96 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_096_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 10 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 0 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 0 10 10, g32p_row17_traceSegment_096_0000_0010, g32p_row17_traceSegment_096_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 20 10 10, g32p_row17_traceSegment_096_0020_0010, g32p_row17_traceSegment_096_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 0 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 0 20 20, g32p_row17_traceSegment_096_0000_0020, g32p_row17_traceSegment_096_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 40 10 10, g32p_row17_traceSegment_096_0040_0010, g32p_row17_traceSegment_096_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 60 10 11, g32p_row17_traceSegment_096_0060_0010, g32p_row17_traceSegment_096_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 40 20 21, g32p_row17_traceSegment_096_0040_0020, g32p_row17_traceSegment_096_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 0 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 0 40 41, g32p_row17_traceSegment_096_0000_0040, g32p_row17_traceSegment_096_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 81 10 10, g32p_row17_traceSegment_096_0081_0010, g32p_row17_traceSegment_096_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 101 10 10, g32p_row17_traceSegment_096_0101_0010, g32p_row17_traceSegment_096_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 81 20 20, g32p_row17_traceSegment_096_0081_0020, g32p_row17_traceSegment_096_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 121 10 10, g32p_row17_traceSegment_096_0121_0010, g32p_row17_traceSegment_096_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 141 10 11, g32p_row17_traceSegment_096_0141_0010, g32p_row17_traceSegment_096_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 121 20 21, g32p_row17_traceSegment_096_0121_0020, g32p_row17_traceSegment_096_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 81 40 41, g32p_row17_traceSegment_096_0081_0040, g32p_row17_traceSegment_096_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_096 0 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 0 81 81, g32p_row17_traceSegment_096_0000_0081, g32p_row17_traceSegment_096_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 162 10 10, g32p_row17_traceSegment_096_0162_0010, g32p_row17_traceSegment_096_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 182 10 10, g32p_row17_traceSegment_096_0182_0010, g32p_row17_traceSegment_096_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 162 20 20, g32p_row17_traceSegment_096_0162_0020, g32p_row17_traceSegment_096_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 202 10 10, g32p_row17_traceSegment_096_0202_0010, g32p_row17_traceSegment_096_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 222 10 11, g32p_row17_traceSegment_096_0222_0010, g32p_row17_traceSegment_096_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 202 20 21, g32p_row17_traceSegment_096_0202_0020, g32p_row17_traceSegment_096_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 162 40 41, g32p_row17_traceSegment_096_0162_0040, g32p_row17_traceSegment_096_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 243 10 10, g32p_row17_traceSegment_096_0243_0010, g32p_row17_traceSegment_096_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 263 10 10, g32p_row17_traceSegment_096_0263_0010, g32p_row17_traceSegment_096_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 243 20 20, g32p_row17_traceSegment_096_0243_0020, g32p_row17_traceSegment_096_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 283 10 10, g32p_row17_traceSegment_096_0283_0010, g32p_row17_traceSegment_096_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 303 10 11, g32p_row17_traceSegment_096_0303_0010, g32p_row17_traceSegment_096_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 283 20 21, g32p_row17_traceSegment_096_0283_0020, g32p_row17_traceSegment_096_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 243 40 41, g32p_row17_traceSegment_096_0243_0040, g32p_row17_traceSegment_096_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_096 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 162 81 81, g32p_row17_traceSegment_096_0162_0081, g32p_row17_traceSegment_096_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_096 0 324 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 0 162 162, g32p_row17_traceSegment_096_0000_0162, g32p_row17_traceSegment_096_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 324 10 10, g32p_row17_traceSegment_096_0324_0010, g32p_row17_traceSegment_096_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 344 10 10, g32p_row17_traceSegment_096_0344_0010, g32p_row17_traceSegment_096_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 324 20 20, g32p_row17_traceSegment_096_0324_0020, g32p_row17_traceSegment_096_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 364 10 10, g32p_row17_traceSegment_096_0364_0010, g32p_row17_traceSegment_096_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 384 10 11, g32p_row17_traceSegment_096_0384_0010, g32p_row17_traceSegment_096_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 364 20 21, g32p_row17_traceSegment_096_0364_0020, g32p_row17_traceSegment_096_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 324 40 41, g32p_row17_traceSegment_096_0324_0040, g32p_row17_traceSegment_096_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 405 10 10, g32p_row17_traceSegment_096_0405_0010, g32p_row17_traceSegment_096_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 425 10 10, g32p_row17_traceSegment_096_0425_0010, g32p_row17_traceSegment_096_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 405 20 20, g32p_row17_traceSegment_096_0405_0020, g32p_row17_traceSegment_096_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 445 10 10, g32p_row17_traceSegment_096_0445_0010, g32p_row17_traceSegment_096_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 465 10 11, g32p_row17_traceSegment_096_0465_0010, g32p_row17_traceSegment_096_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 445 20 21, g32p_row17_traceSegment_096_0445_0020, g32p_row17_traceSegment_096_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 405 40 41, g32p_row17_traceSegment_096_0405_0040, g32p_row17_traceSegment_096_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_096 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 324 81 81, g32p_row17_traceSegment_096_0324_0081, g32p_row17_traceSegment_096_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 486 10 10, g32p_row17_traceSegment_096_0486_0010, g32p_row17_traceSegment_096_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 506 10 10, g32p_row17_traceSegment_096_0506_0010, g32p_row17_traceSegment_096_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 486 20 20, g32p_row17_traceSegment_096_0486_0020, g32p_row17_traceSegment_096_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 526 10 10, g32p_row17_traceSegment_096_0526_0010, g32p_row17_traceSegment_096_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 546 10 11, g32p_row17_traceSegment_096_0546_0010, g32p_row17_traceSegment_096_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 526 20 21, g32p_row17_traceSegment_096_0526_0020, g32p_row17_traceSegment_096_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 486 40 41, g32p_row17_traceSegment_096_0486_0040, g32p_row17_traceSegment_096_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 567 10 10, g32p_row17_traceSegment_096_0567_0010, g32p_row17_traceSegment_096_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 587 10 10, g32p_row17_traceSegment_096_0587_0010, g32p_row17_traceSegment_096_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 567 20 20, g32p_row17_traceSegment_096_0567_0020, g32p_row17_traceSegment_096_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 607 10 10, g32p_row17_traceSegment_096_0607_0010, g32p_row17_traceSegment_096_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 627 10 11, g32p_row17_traceSegment_096_0627_0010, g32p_row17_traceSegment_096_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 607 20 21, g32p_row17_traceSegment_096_0607_0020, g32p_row17_traceSegment_096_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 567 40 41, g32p_row17_traceSegment_096_0567_0040, g32p_row17_traceSegment_096_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_096 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 486 81 81, g32p_row17_traceSegment_096_0486_0081, g32p_row17_traceSegment_096_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_096 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 324 162 162, g32p_row17_traceSegment_096_0324_0162, g32p_row17_traceSegment_096_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_096 0 648 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 0 324 324, g32p_row17_traceSegment_096_0000_0324, g32p_row17_traceSegment_096_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 648 10 10, g32p_row17_traceSegment_096_0648_0010, g32p_row17_traceSegment_096_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 668 10 10, g32p_row17_traceSegment_096_0668_0010, g32p_row17_traceSegment_096_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 648 20 20, g32p_row17_traceSegment_096_0648_0020, g32p_row17_traceSegment_096_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 688 10 10, g32p_row17_traceSegment_096_0688_0010, g32p_row17_traceSegment_096_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 708 10 11, g32p_row17_traceSegment_096_0708_0010, g32p_row17_traceSegment_096_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 688 20 21, g32p_row17_traceSegment_096_0688_0020, g32p_row17_traceSegment_096_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 648 40 41, g32p_row17_traceSegment_096_0648_0040, g32p_row17_traceSegment_096_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 729 10 10, g32p_row17_traceSegment_096_0729_0010, g32p_row17_traceSegment_096_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 749 10 10, g32p_row17_traceSegment_096_0749_0010, g32p_row17_traceSegment_096_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 729 20 20, g32p_row17_traceSegment_096_0729_0020, g32p_row17_traceSegment_096_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 769 10 10, g32p_row17_traceSegment_096_0769_0010, g32p_row17_traceSegment_096_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 789 10 11, g32p_row17_traceSegment_096_0789_0010, g32p_row17_traceSegment_096_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 769 20 21, g32p_row17_traceSegment_096_0769_0020, g32p_row17_traceSegment_096_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 729 40 41, g32p_row17_traceSegment_096_0729_0040, g32p_row17_traceSegment_096_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_096 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 648 81 81, g32p_row17_traceSegment_096_0648_0081, g32p_row17_traceSegment_096_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 810 10 10, g32p_row17_traceSegment_096_0810_0010, g32p_row17_traceSegment_096_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 830 10 10, g32p_row17_traceSegment_096_0830_0010, g32p_row17_traceSegment_096_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 810 20 20, g32p_row17_traceSegment_096_0810_0020, g32p_row17_traceSegment_096_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 850 10 10, g32p_row17_traceSegment_096_0850_0010, g32p_row17_traceSegment_096_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 870 10 11, g32p_row17_traceSegment_096_0870_0010, g32p_row17_traceSegment_096_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 850 20 21, g32p_row17_traceSegment_096_0850_0020, g32p_row17_traceSegment_096_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 810 40 41, g32p_row17_traceSegment_096_0810_0040, g32p_row17_traceSegment_096_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 891 10 10, g32p_row17_traceSegment_096_0891_0010, g32p_row17_traceSegment_096_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 911 10 10, g32p_row17_traceSegment_096_0911_0010, g32p_row17_traceSegment_096_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 891 20 20, g32p_row17_traceSegment_096_0891_0020, g32p_row17_traceSegment_096_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 931 10 10, g32p_row17_traceSegment_096_0931_0010, g32p_row17_traceSegment_096_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 951 10 11, g32p_row17_traceSegment_096_0951_0010, g32p_row17_traceSegment_096_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 931 20 21, g32p_row17_traceSegment_096_0931_0020, g32p_row17_traceSegment_096_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 891 40 41, g32p_row17_traceSegment_096_0891_0040, g32p_row17_traceSegment_096_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_096 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 810 81 81, g32p_row17_traceSegment_096_0810_0081, g32p_row17_traceSegment_096_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_096 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 648 162 162, g32p_row17_traceSegment_096_0648_0162, g32p_row17_traceSegment_096_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 972 10 10, g32p_row17_traceSegment_096_0972_0010, g32p_row17_traceSegment_096_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 992 10 10, g32p_row17_traceSegment_096_0992_0010, g32p_row17_traceSegment_096_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 972 20 20, g32p_row17_traceSegment_096_0972_0020, g32p_row17_traceSegment_096_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1012 10 10, g32p_row17_traceSegment_096_1012_0010, g32p_row17_traceSegment_096_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1032 10 11, g32p_row17_traceSegment_096_1032_0010, g32p_row17_traceSegment_096_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1012 20 21, g32p_row17_traceSegment_096_1012_0020, g32p_row17_traceSegment_096_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 972 40 41, g32p_row17_traceSegment_096_0972_0040, g32p_row17_traceSegment_096_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1053 10 10, g32p_row17_traceSegment_096_1053_0010, g32p_row17_traceSegment_096_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1073 10 10, g32p_row17_traceSegment_096_1073_0010, g32p_row17_traceSegment_096_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1053 20 20, g32p_row17_traceSegment_096_1053_0020, g32p_row17_traceSegment_096_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1093 10 10, g32p_row17_traceSegment_096_1093_0010, g32p_row17_traceSegment_096_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1113 10 11, g32p_row17_traceSegment_096_1113_0010, g32p_row17_traceSegment_096_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1093 20 21, g32p_row17_traceSegment_096_1093_0020, g32p_row17_traceSegment_096_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1053 40 41, g32p_row17_traceSegment_096_1053_0040, g32p_row17_traceSegment_096_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_096 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 972 81 81, g32p_row17_traceSegment_096_0972_0081, g32p_row17_traceSegment_096_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1134 10 10, g32p_row17_traceSegment_096_1134_0010, g32p_row17_traceSegment_096_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1154 10 10, g32p_row17_traceSegment_096_1154_0010, g32p_row17_traceSegment_096_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1134 20 20, g32p_row17_traceSegment_096_1134_0020, g32p_row17_traceSegment_096_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1174 10 10, g32p_row17_traceSegment_096_1174_0010, g32p_row17_traceSegment_096_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1194 10 11, g32p_row17_traceSegment_096_1194_0010, g32p_row17_traceSegment_096_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1174 20 21, g32p_row17_traceSegment_096_1174_0020, g32p_row17_traceSegment_096_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1134 40 41, g32p_row17_traceSegment_096_1134_0040, g32p_row17_traceSegment_096_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1215 10 10, g32p_row17_traceSegment_096_1215_0010, g32p_row17_traceSegment_096_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1235 10 10, g32p_row17_traceSegment_096_1235_0010, g32p_row17_traceSegment_096_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_096 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1215 20 20, g32p_row17_traceSegment_096_1215_0020, g32p_row17_traceSegment_096_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_096 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1255 10 10, g32p_row17_traceSegment_096_1255_0010, g32p_row17_traceSegment_096_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_096 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_096 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_096_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_096 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1275 10 11, g32p_row17_traceSegment_096_1275_0010, g32p_row17_traceSegment_096_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_096 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1255 20 21, g32p_row17_traceSegment_096_1255_0020, g32p_row17_traceSegment_096_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_096 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1215 40 41, g32p_row17_traceSegment_096_1215_0040, g32p_row17_traceSegment_096_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_096_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_096 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 1134 81 81, g32p_row17_traceSegment_096_1134_0081, g32p_row17_traceSegment_096_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_096 972 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 972 162 162, g32p_row17_traceSegment_096_0972_0162, g32p_row17_traceSegment_096_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_096 648 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 648 324 324, g32p_row17_traceSegment_096_0648_0324, g32p_row17_traceSegment_096_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_096_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_096 0 1296 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_096 0 648 648, g32p_row17_traceSegment_096_0000_0648, g32p_row17_traceSegment_096_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 96 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_096_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_097 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 97 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_097_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 0 10 10, g32p_row17_traceSegment_097_0000_0010, g32p_row17_traceSegment_097_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 20 10 10, g32p_row17_traceSegment_097_0020_0010, g32p_row17_traceSegment_097_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 0 20 20, g32p_row17_traceSegment_097_0000_0020, g32p_row17_traceSegment_097_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 40 10 10, g32p_row17_traceSegment_097_0040_0010, g32p_row17_traceSegment_097_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 60 10 11, g32p_row17_traceSegment_097_0060_0010, g32p_row17_traceSegment_097_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 40 20 21, g32p_row17_traceSegment_097_0040_0020, g32p_row17_traceSegment_097_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 0 40 41, g32p_row17_traceSegment_097_0000_0040, g32p_row17_traceSegment_097_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 81 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 81 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 81 10 10, g32p_row17_traceSegment_097_0081_0010, g32p_row17_traceSegment_097_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 101 10 10, g32p_row17_traceSegment_097_0101_0010, g32p_row17_traceSegment_097_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 81 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 81 20 20, g32p_row17_traceSegment_097_0081_0020, g32p_row17_traceSegment_097_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 121 10 10, g32p_row17_traceSegment_097_0121_0010, g32p_row17_traceSegment_097_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 141 10 11, g32p_row17_traceSegment_097_0141_0010, g32p_row17_traceSegment_097_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 121 20 21, g32p_row17_traceSegment_097_0121_0020, g32p_row17_traceSegment_097_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 81 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 81 40 41, g32p_row17_traceSegment_097_0081_0040, g32p_row17_traceSegment_097_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_097 0 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 0 81 81, g32p_row17_traceSegment_097_0000_0081, g32p_row17_traceSegment_097_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 162 10 10, g32p_row17_traceSegment_097_0162_0010, g32p_row17_traceSegment_097_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 182 10 10, g32p_row17_traceSegment_097_0182_0010, g32p_row17_traceSegment_097_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 162 20 20, g32p_row17_traceSegment_097_0162_0020, g32p_row17_traceSegment_097_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 202 10 10, g32p_row17_traceSegment_097_0202_0010, g32p_row17_traceSegment_097_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 222 10 11, g32p_row17_traceSegment_097_0222_0010, g32p_row17_traceSegment_097_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 202 20 21, g32p_row17_traceSegment_097_0202_0020, g32p_row17_traceSegment_097_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 162 40 41, g32p_row17_traceSegment_097_0162_0040, g32p_row17_traceSegment_097_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 243 10 10, g32p_row17_traceSegment_097_0243_0010, g32p_row17_traceSegment_097_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 263 10 10, g32p_row17_traceSegment_097_0263_0010, g32p_row17_traceSegment_097_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 243 20 20, g32p_row17_traceSegment_097_0243_0020, g32p_row17_traceSegment_097_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 283 10 10, g32p_row17_traceSegment_097_0283_0010, g32p_row17_traceSegment_097_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 303 10 11, g32p_row17_traceSegment_097_0303_0010, g32p_row17_traceSegment_097_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 283 20 21, g32p_row17_traceSegment_097_0283_0020, g32p_row17_traceSegment_097_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 243 40 41, g32p_row17_traceSegment_097_0243_0040, g32p_row17_traceSegment_097_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_097 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 162 81 81, g32p_row17_traceSegment_097_0162_0081, g32p_row17_traceSegment_097_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_097 0 324 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 0 162 162, g32p_row17_traceSegment_097_0000_0162, g32p_row17_traceSegment_097_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 324 10 10, g32p_row17_traceSegment_097_0324_0010, g32p_row17_traceSegment_097_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 344 10 10, g32p_row17_traceSegment_097_0344_0010, g32p_row17_traceSegment_097_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 324 20 20, g32p_row17_traceSegment_097_0324_0020, g32p_row17_traceSegment_097_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 364 10 10, g32p_row17_traceSegment_097_0364_0010, g32p_row17_traceSegment_097_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 384 10 11, g32p_row17_traceSegment_097_0384_0010, g32p_row17_traceSegment_097_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 364 20 21, g32p_row17_traceSegment_097_0364_0020, g32p_row17_traceSegment_097_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 324 40 41, g32p_row17_traceSegment_097_0324_0040, g32p_row17_traceSegment_097_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 405 10 10, g32p_row17_traceSegment_097_0405_0010, g32p_row17_traceSegment_097_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 425 10 10, g32p_row17_traceSegment_097_0425_0010, g32p_row17_traceSegment_097_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 405 20 20, g32p_row17_traceSegment_097_0405_0020, g32p_row17_traceSegment_097_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 445 10 10, g32p_row17_traceSegment_097_0445_0010, g32p_row17_traceSegment_097_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 465 10 11, g32p_row17_traceSegment_097_0465_0010, g32p_row17_traceSegment_097_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 445 20 21, g32p_row17_traceSegment_097_0445_0020, g32p_row17_traceSegment_097_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 405 40 41, g32p_row17_traceSegment_097_0405_0040, g32p_row17_traceSegment_097_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_097 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 324 81 81, g32p_row17_traceSegment_097_0324_0081, g32p_row17_traceSegment_097_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 486 10 10, g32p_row17_traceSegment_097_0486_0010, g32p_row17_traceSegment_097_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 506 10 10, g32p_row17_traceSegment_097_0506_0010, g32p_row17_traceSegment_097_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 486 20 20, g32p_row17_traceSegment_097_0486_0020, g32p_row17_traceSegment_097_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 526 10 10, g32p_row17_traceSegment_097_0526_0010, g32p_row17_traceSegment_097_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 546 10 11, g32p_row17_traceSegment_097_0546_0010, g32p_row17_traceSegment_097_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 526 20 21, g32p_row17_traceSegment_097_0526_0020, g32p_row17_traceSegment_097_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 486 40 41, g32p_row17_traceSegment_097_0486_0040, g32p_row17_traceSegment_097_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 567 10 10, g32p_row17_traceSegment_097_0567_0010, g32p_row17_traceSegment_097_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 587 10 10, g32p_row17_traceSegment_097_0587_0010, g32p_row17_traceSegment_097_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 567 20 20, g32p_row17_traceSegment_097_0567_0020, g32p_row17_traceSegment_097_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 607 10 10, g32p_row17_traceSegment_097_0607_0010, g32p_row17_traceSegment_097_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 627 10 11, g32p_row17_traceSegment_097_0627_0010, g32p_row17_traceSegment_097_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 607 20 21, g32p_row17_traceSegment_097_0607_0020, g32p_row17_traceSegment_097_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 567 40 41, g32p_row17_traceSegment_097_0567_0040, g32p_row17_traceSegment_097_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_097 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 486 81 81, g32p_row17_traceSegment_097_0486_0081, g32p_row17_traceSegment_097_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_097 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 324 162 162, g32p_row17_traceSegment_097_0324_0162, g32p_row17_traceSegment_097_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_097 0 648 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 0 324 324, g32p_row17_traceSegment_097_0000_0324, g32p_row17_traceSegment_097_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 648 10 10, g32p_row17_traceSegment_097_0648_0010, g32p_row17_traceSegment_097_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 668 10 10, g32p_row17_traceSegment_097_0668_0010, g32p_row17_traceSegment_097_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 648 20 20, g32p_row17_traceSegment_097_0648_0020, g32p_row17_traceSegment_097_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 688 10 10, g32p_row17_traceSegment_097_0688_0010, g32p_row17_traceSegment_097_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 708 10 11, g32p_row17_traceSegment_097_0708_0010, g32p_row17_traceSegment_097_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 688 20 21, g32p_row17_traceSegment_097_0688_0020, g32p_row17_traceSegment_097_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 648 40 41, g32p_row17_traceSegment_097_0648_0040, g32p_row17_traceSegment_097_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 729 10 10, g32p_row17_traceSegment_097_0729_0010, g32p_row17_traceSegment_097_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 749 10 10, g32p_row17_traceSegment_097_0749_0010, g32p_row17_traceSegment_097_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 729 20 20, g32p_row17_traceSegment_097_0729_0020, g32p_row17_traceSegment_097_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 769 10 10, g32p_row17_traceSegment_097_0769_0010, g32p_row17_traceSegment_097_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 789 10 11, g32p_row17_traceSegment_097_0789_0010, g32p_row17_traceSegment_097_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 769 20 21, g32p_row17_traceSegment_097_0769_0020, g32p_row17_traceSegment_097_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 729 40 41, g32p_row17_traceSegment_097_0729_0040, g32p_row17_traceSegment_097_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_097 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 648 81 81, g32p_row17_traceSegment_097_0648_0081, g32p_row17_traceSegment_097_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 810 10 10, g32p_row17_traceSegment_097_0810_0010, g32p_row17_traceSegment_097_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 830 10 10, g32p_row17_traceSegment_097_0830_0010, g32p_row17_traceSegment_097_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 810 20 20, g32p_row17_traceSegment_097_0810_0020, g32p_row17_traceSegment_097_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 850 10 10, g32p_row17_traceSegment_097_0850_0010, g32p_row17_traceSegment_097_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 870 10 11, g32p_row17_traceSegment_097_0870_0010, g32p_row17_traceSegment_097_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 850 20 21, g32p_row17_traceSegment_097_0850_0020, g32p_row17_traceSegment_097_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 810 40 41, g32p_row17_traceSegment_097_0810_0040, g32p_row17_traceSegment_097_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 891 10 10, g32p_row17_traceSegment_097_0891_0010, g32p_row17_traceSegment_097_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 911 10 10, g32p_row17_traceSegment_097_0911_0010, g32p_row17_traceSegment_097_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 891 20 20, g32p_row17_traceSegment_097_0891_0020, g32p_row17_traceSegment_097_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 931 10 10, g32p_row17_traceSegment_097_0931_0010, g32p_row17_traceSegment_097_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 951 10 11, g32p_row17_traceSegment_097_0951_0010, g32p_row17_traceSegment_097_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 931 20 21, g32p_row17_traceSegment_097_0931_0020, g32p_row17_traceSegment_097_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 891 40 41, g32p_row17_traceSegment_097_0891_0040, g32p_row17_traceSegment_097_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_097 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 810 81 81, g32p_row17_traceSegment_097_0810_0081, g32p_row17_traceSegment_097_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_097 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 648 162 162, g32p_row17_traceSegment_097_0648_0162, g32p_row17_traceSegment_097_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 972 10 10, g32p_row17_traceSegment_097_0972_0010, g32p_row17_traceSegment_097_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 992 10 10, g32p_row17_traceSegment_097_0992_0010, g32p_row17_traceSegment_097_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 972 20 20, g32p_row17_traceSegment_097_0972_0020, g32p_row17_traceSegment_097_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1012 10 10, g32p_row17_traceSegment_097_1012_0010, g32p_row17_traceSegment_097_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1032 10 11, g32p_row17_traceSegment_097_1032_0010, g32p_row17_traceSegment_097_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1012 20 21, g32p_row17_traceSegment_097_1012_0020, g32p_row17_traceSegment_097_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 972 40 41, g32p_row17_traceSegment_097_0972_0040, g32p_row17_traceSegment_097_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1053 10 10, g32p_row17_traceSegment_097_1053_0010, g32p_row17_traceSegment_097_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1073 10 10, g32p_row17_traceSegment_097_1073_0010, g32p_row17_traceSegment_097_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1053 20 20, g32p_row17_traceSegment_097_1053_0020, g32p_row17_traceSegment_097_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1093 10 10, g32p_row17_traceSegment_097_1093_0010, g32p_row17_traceSegment_097_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1113 10 11, g32p_row17_traceSegment_097_1113_0010, g32p_row17_traceSegment_097_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1093 20 21, g32p_row17_traceSegment_097_1093_0020, g32p_row17_traceSegment_097_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1053 40 41, g32p_row17_traceSegment_097_1053_0040, g32p_row17_traceSegment_097_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_097 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 972 81 81, g32p_row17_traceSegment_097_0972_0081, g32p_row17_traceSegment_097_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1134 10 10, g32p_row17_traceSegment_097_1134_0010, g32p_row17_traceSegment_097_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1154 10 10, g32p_row17_traceSegment_097_1154_0010, g32p_row17_traceSegment_097_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1134 20 20, g32p_row17_traceSegment_097_1134_0020, g32p_row17_traceSegment_097_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1174 10 10, g32p_row17_traceSegment_097_1174_0010, g32p_row17_traceSegment_097_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1194 10 11, g32p_row17_traceSegment_097_1194_0010, g32p_row17_traceSegment_097_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1174 20 21, g32p_row17_traceSegment_097_1174_0020, g32p_row17_traceSegment_097_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1134 40 41, g32p_row17_traceSegment_097_1134_0040, g32p_row17_traceSegment_097_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1215 10 10, g32p_row17_traceSegment_097_1215_0010, g32p_row17_traceSegment_097_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1235 10 10, g32p_row17_traceSegment_097_1235_0010, g32p_row17_traceSegment_097_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_097 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1215 20 20, g32p_row17_traceSegment_097_1215_0020, g32p_row17_traceSegment_097_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_097 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1255 10 10, g32p_row17_traceSegment_097_1255_0010, g32p_row17_traceSegment_097_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_097 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_097 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_097_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_097 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1275 10 11, g32p_row17_traceSegment_097_1275_0010, g32p_row17_traceSegment_097_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_097 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1255 20 21, g32p_row17_traceSegment_097_1255_0020, g32p_row17_traceSegment_097_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_097 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1215 40 41, g32p_row17_traceSegment_097_1215_0040, g32p_row17_traceSegment_097_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_097_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_097 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 1134 81 81, g32p_row17_traceSegment_097_1134_0081, g32p_row17_traceSegment_097_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_097 972 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 972 162 162, g32p_row17_traceSegment_097_0972_0162, g32p_row17_traceSegment_097_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_097 648 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 648 324 324, g32p_row17_traceSegment_097_0648_0324, g32p_row17_traceSegment_097_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_097_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_097 0 1296 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_097 0 648 648, g32p_row17_traceSegment_097_0000_0648, g32p_row17_traceSegment_097_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 97 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_097_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_098 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 98 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_098_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 0 10 10, g32p_row17_traceSegment_098_0000_0010, g32p_row17_traceSegment_098_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 20 10 10, g32p_row17_traceSegment_098_0020_0010, g32p_row17_traceSegment_098_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 0 20 20, g32p_row17_traceSegment_098_0000_0020, g32p_row17_traceSegment_098_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 40 10 10, g32p_row17_traceSegment_098_0040_0010, g32p_row17_traceSegment_098_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 60 10 11, g32p_row17_traceSegment_098_0060_0010, g32p_row17_traceSegment_098_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 40 20 21, g32p_row17_traceSegment_098_0040_0020, g32p_row17_traceSegment_098_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 0 40 41, g32p_row17_traceSegment_098_0000_0040, g32p_row17_traceSegment_098_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 81 10 10, g32p_row17_traceSegment_098_0081_0010, g32p_row17_traceSegment_098_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 101 10 10, g32p_row17_traceSegment_098_0101_0010, g32p_row17_traceSegment_098_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 81 20 20, g32p_row17_traceSegment_098_0081_0020, g32p_row17_traceSegment_098_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 121 10 10, g32p_row17_traceSegment_098_0121_0010, g32p_row17_traceSegment_098_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 141 10 11, g32p_row17_traceSegment_098_0141_0010, g32p_row17_traceSegment_098_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 121 20 21, g32p_row17_traceSegment_098_0121_0020, g32p_row17_traceSegment_098_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 81 40 41, g32p_row17_traceSegment_098_0081_0040, g32p_row17_traceSegment_098_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_098 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 0 81 81, g32p_row17_traceSegment_098_0000_0081, g32p_row17_traceSegment_098_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 162 10 10, g32p_row17_traceSegment_098_0162_0010, g32p_row17_traceSegment_098_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 182 10 10, g32p_row17_traceSegment_098_0182_0010, g32p_row17_traceSegment_098_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 162 20 20, g32p_row17_traceSegment_098_0162_0020, g32p_row17_traceSegment_098_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 202 10 10, g32p_row17_traceSegment_098_0202_0010, g32p_row17_traceSegment_098_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 222 10 11, g32p_row17_traceSegment_098_0222_0010, g32p_row17_traceSegment_098_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 202 20 21, g32p_row17_traceSegment_098_0202_0020, g32p_row17_traceSegment_098_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 162 40 41, g32p_row17_traceSegment_098_0162_0040, g32p_row17_traceSegment_098_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 243 10 10, g32p_row17_traceSegment_098_0243_0010, g32p_row17_traceSegment_098_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 263 10 10, g32p_row17_traceSegment_098_0263_0010, g32p_row17_traceSegment_098_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 243 20 20, g32p_row17_traceSegment_098_0243_0020, g32p_row17_traceSegment_098_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 283 10 10, g32p_row17_traceSegment_098_0283_0010, g32p_row17_traceSegment_098_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 303 10 11, g32p_row17_traceSegment_098_0303_0010, g32p_row17_traceSegment_098_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 283 20 21, g32p_row17_traceSegment_098_0283_0020, g32p_row17_traceSegment_098_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 243 40 41, g32p_row17_traceSegment_098_0243_0040, g32p_row17_traceSegment_098_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_098 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 162 81 81, g32p_row17_traceSegment_098_0162_0081, g32p_row17_traceSegment_098_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_098 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 0 162 162, g32p_row17_traceSegment_098_0000_0162, g32p_row17_traceSegment_098_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 324 10 10, g32p_row17_traceSegment_098_0324_0010, g32p_row17_traceSegment_098_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 344 10 10, g32p_row17_traceSegment_098_0344_0010, g32p_row17_traceSegment_098_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 324 20 20, g32p_row17_traceSegment_098_0324_0020, g32p_row17_traceSegment_098_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 364 10 10, g32p_row17_traceSegment_098_0364_0010, g32p_row17_traceSegment_098_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 384 10 11, g32p_row17_traceSegment_098_0384_0010, g32p_row17_traceSegment_098_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 364 20 21, g32p_row17_traceSegment_098_0364_0020, g32p_row17_traceSegment_098_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 324 40 41, g32p_row17_traceSegment_098_0324_0040, g32p_row17_traceSegment_098_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 405 10 10, g32p_row17_traceSegment_098_0405_0010, g32p_row17_traceSegment_098_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 425 10 10, g32p_row17_traceSegment_098_0425_0010, g32p_row17_traceSegment_098_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 405 20 20, g32p_row17_traceSegment_098_0405_0020, g32p_row17_traceSegment_098_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 445 10 10, g32p_row17_traceSegment_098_0445_0010, g32p_row17_traceSegment_098_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 465 10 11, g32p_row17_traceSegment_098_0465_0010, g32p_row17_traceSegment_098_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 445 20 21, g32p_row17_traceSegment_098_0445_0020, g32p_row17_traceSegment_098_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 405 40 41, g32p_row17_traceSegment_098_0405_0040, g32p_row17_traceSegment_098_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_098 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 324 81 81, g32p_row17_traceSegment_098_0324_0081, g32p_row17_traceSegment_098_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 486 10 10, g32p_row17_traceSegment_098_0486_0010, g32p_row17_traceSegment_098_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 506 10 10, g32p_row17_traceSegment_098_0506_0010, g32p_row17_traceSegment_098_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 486 20 20, g32p_row17_traceSegment_098_0486_0020, g32p_row17_traceSegment_098_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 526 10 10, g32p_row17_traceSegment_098_0526_0010, g32p_row17_traceSegment_098_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 546 10 11, g32p_row17_traceSegment_098_0546_0010, g32p_row17_traceSegment_098_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 526 20 21, g32p_row17_traceSegment_098_0526_0020, g32p_row17_traceSegment_098_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 486 40 41, g32p_row17_traceSegment_098_0486_0040, g32p_row17_traceSegment_098_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 567 10 10, g32p_row17_traceSegment_098_0567_0010, g32p_row17_traceSegment_098_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 587 10 10, g32p_row17_traceSegment_098_0587_0010, g32p_row17_traceSegment_098_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 567 20 20, g32p_row17_traceSegment_098_0567_0020, g32p_row17_traceSegment_098_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 607 10 10, g32p_row17_traceSegment_098_0607_0010, g32p_row17_traceSegment_098_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 627 10 11, g32p_row17_traceSegment_098_0627_0010, g32p_row17_traceSegment_098_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 607 20 21, g32p_row17_traceSegment_098_0607_0020, g32p_row17_traceSegment_098_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 567 40 41, g32p_row17_traceSegment_098_0567_0040, g32p_row17_traceSegment_098_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_098 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 486 81 81, g32p_row17_traceSegment_098_0486_0081, g32p_row17_traceSegment_098_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_098 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 324 162 162, g32p_row17_traceSegment_098_0324_0162, g32p_row17_traceSegment_098_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_098 0 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 0 324 324, g32p_row17_traceSegment_098_0000_0324, g32p_row17_traceSegment_098_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 648 10 10, g32p_row17_traceSegment_098_0648_0010, g32p_row17_traceSegment_098_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 668 10 10, g32p_row17_traceSegment_098_0668_0010, g32p_row17_traceSegment_098_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 648 20 20, g32p_row17_traceSegment_098_0648_0020, g32p_row17_traceSegment_098_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 688 10 10, g32p_row17_traceSegment_098_0688_0010, g32p_row17_traceSegment_098_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 708 10 11, g32p_row17_traceSegment_098_0708_0010, g32p_row17_traceSegment_098_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 688 20 21, g32p_row17_traceSegment_098_0688_0020, g32p_row17_traceSegment_098_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 648 40 41, g32p_row17_traceSegment_098_0648_0040, g32p_row17_traceSegment_098_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 729 10 10, g32p_row17_traceSegment_098_0729_0010, g32p_row17_traceSegment_098_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 749 10 10, g32p_row17_traceSegment_098_0749_0010, g32p_row17_traceSegment_098_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 729 20 20, g32p_row17_traceSegment_098_0729_0020, g32p_row17_traceSegment_098_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 769 10 10, g32p_row17_traceSegment_098_0769_0010, g32p_row17_traceSegment_098_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 789 10 11, g32p_row17_traceSegment_098_0789_0010, g32p_row17_traceSegment_098_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 769 20 21, g32p_row17_traceSegment_098_0769_0020, g32p_row17_traceSegment_098_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 729 40 41, g32p_row17_traceSegment_098_0729_0040, g32p_row17_traceSegment_098_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_098 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 648 81 81, g32p_row17_traceSegment_098_0648_0081, g32p_row17_traceSegment_098_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 810 10 10, g32p_row17_traceSegment_098_0810_0010, g32p_row17_traceSegment_098_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 830 10 10, g32p_row17_traceSegment_098_0830_0010, g32p_row17_traceSegment_098_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 810 20 20, g32p_row17_traceSegment_098_0810_0020, g32p_row17_traceSegment_098_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 850 10 10, g32p_row17_traceSegment_098_0850_0010, g32p_row17_traceSegment_098_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 870 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 870 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 870 10 11, g32p_row17_traceSegment_098_0870_0010, g32p_row17_traceSegment_098_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 850 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 850 20 21, g32p_row17_traceSegment_098_0850_0020, g32p_row17_traceSegment_098_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 810 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 810 40 41, g32p_row17_traceSegment_098_0810_0040, g32p_row17_traceSegment_098_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 891 10 10, g32p_row17_traceSegment_098_0891_0010, g32p_row17_traceSegment_098_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 911 10 10, g32p_row17_traceSegment_098_0911_0010, g32p_row17_traceSegment_098_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 891 20 20, g32p_row17_traceSegment_098_0891_0020, g32p_row17_traceSegment_098_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 931 10 10, g32p_row17_traceSegment_098_0931_0010, g32p_row17_traceSegment_098_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 951 10 11, g32p_row17_traceSegment_098_0951_0010, g32p_row17_traceSegment_098_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 931 20 21, g32p_row17_traceSegment_098_0931_0020, g32p_row17_traceSegment_098_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 891 40 41, g32p_row17_traceSegment_098_0891_0040, g32p_row17_traceSegment_098_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_098 810 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 810 81 81, g32p_row17_traceSegment_098_0810_0081, g32p_row17_traceSegment_098_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_098 648 324 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 648 162 162, g32p_row17_traceSegment_098_0648_0162, g32p_row17_traceSegment_098_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 972 10 10, g32p_row17_traceSegment_098_0972_0010, g32p_row17_traceSegment_098_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 992 10 10, g32p_row17_traceSegment_098_0992_0010, g32p_row17_traceSegment_098_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 972 20 20, g32p_row17_traceSegment_098_0972_0020, g32p_row17_traceSegment_098_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1012 10 10, g32p_row17_traceSegment_098_1012_0010, g32p_row17_traceSegment_098_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1032 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 1032 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1032 10 11, g32p_row17_traceSegment_098_1032_0010, g32p_row17_traceSegment_098_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 1012 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1012 20 21, g32p_row17_traceSegment_098_1012_0020, g32p_row17_traceSegment_098_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 972 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 972 40 41, g32p_row17_traceSegment_098_0972_0040, g32p_row17_traceSegment_098_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1063 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 1053 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1053 10 10, g32p_row17_traceSegment_098_1053_0010, g32p_row17_traceSegment_098_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1083 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 1073 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1073 10 10, g32p_row17_traceSegment_098_1073_0010, g32p_row17_traceSegment_098_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 1053 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1053 20 20, g32p_row17_traceSegment_098_1053_0020, g32p_row17_traceSegment_098_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1093 10 10, g32p_row17_traceSegment_098_1093_0010, g32p_row17_traceSegment_098_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1113 10 11, g32p_row17_traceSegment_098_1113_0010, g32p_row17_traceSegment_098_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1093 20 21, g32p_row17_traceSegment_098_1093_0020, g32p_row17_traceSegment_098_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 1053 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1053 40 41, g32p_row17_traceSegment_098_1053_0040, g32p_row17_traceSegment_098_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_098 972 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 972 81 81, g32p_row17_traceSegment_098_0972_0081, g32p_row17_traceSegment_098_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1134 10 10, g32p_row17_traceSegment_098_1134_0010, g32p_row17_traceSegment_098_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1154 10 10, g32p_row17_traceSegment_098_1154_0010, g32p_row17_traceSegment_098_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1134 20 20, g32p_row17_traceSegment_098_1134_0020, g32p_row17_traceSegment_098_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1174 10 10, g32p_row17_traceSegment_098_1174_0010, g32p_row17_traceSegment_098_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1194 10 11, g32p_row17_traceSegment_098_1194_0010, g32p_row17_traceSegment_098_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1174 20 21, g32p_row17_traceSegment_098_1174_0020, g32p_row17_traceSegment_098_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1134 40 41, g32p_row17_traceSegment_098_1134_0040, g32p_row17_traceSegment_098_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1215 10 10, g32p_row17_traceSegment_098_1215_0010, g32p_row17_traceSegment_098_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1235 10 10, g32p_row17_traceSegment_098_1235_0010, g32p_row17_traceSegment_098_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_098 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1215 20 20, g32p_row17_traceSegment_098_1215_0020, g32p_row17_traceSegment_098_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_098 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1255 10 10, g32p_row17_traceSegment_098_1255_0010, g32p_row17_traceSegment_098_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_098 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_098 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_098_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_098 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1275 10 11, g32p_row17_traceSegment_098_1275_0010, g32p_row17_traceSegment_098_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_098 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1255 20 21, g32p_row17_traceSegment_098_1255_0020, g32p_row17_traceSegment_098_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_098 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1215 40 41, g32p_row17_traceSegment_098_1215_0040, g32p_row17_traceSegment_098_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_098_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_098 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 1134 81 81, g32p_row17_traceSegment_098_1134_0081, g32p_row17_traceSegment_098_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_098 972 324 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 972 162 162, g32p_row17_traceSegment_098_0972_0162, g32p_row17_traceSegment_098_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_098 648 648 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 648 324 324, g32p_row17_traceSegment_098_0648_0324, g32p_row17_traceSegment_098_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_098_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_098 0 1296 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_098 0 648 648, g32p_row17_traceSegment_098_0000_0648, g32p_row17_traceSegment_098_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 98 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_098_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_099 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 99 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_099_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 0 10 10, g32p_row17_traceSegment_099_0000_0010, g32p_row17_traceSegment_099_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 20 10 10, g32p_row17_traceSegment_099_0020_0010, g32p_row17_traceSegment_099_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 0 20 20, g32p_row17_traceSegment_099_0000_0020, g32p_row17_traceSegment_099_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 50 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 40 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 40 10 10, g32p_row17_traceSegment_099_0040_0010, g32p_row17_traceSegment_099_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 60 10 11, g32p_row17_traceSegment_099_0060_0010, g32p_row17_traceSegment_099_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 40 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 40 20 21, g32p_row17_traceSegment_099_0040_0020, g32p_row17_traceSegment_099_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 0 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 0 40 41, g32p_row17_traceSegment_099_0000_0040, g32p_row17_traceSegment_099_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 81 10 10, g32p_row17_traceSegment_099_0081_0010, g32p_row17_traceSegment_099_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 101 10 10, g32p_row17_traceSegment_099_0101_0010, g32p_row17_traceSegment_099_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 81 20 20, g32p_row17_traceSegment_099_0081_0020, g32p_row17_traceSegment_099_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 121 10 10, g32p_row17_traceSegment_099_0121_0010, g32p_row17_traceSegment_099_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 141 10 11, g32p_row17_traceSegment_099_0141_0010, g32p_row17_traceSegment_099_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 121 20 21, g32p_row17_traceSegment_099_0121_0020, g32p_row17_traceSegment_099_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 81 40 41, g32p_row17_traceSegment_099_0081_0040, g32p_row17_traceSegment_099_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_099 0 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 0 81 81, g32p_row17_traceSegment_099_0000_0081, g32p_row17_traceSegment_099_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 162 10 10, g32p_row17_traceSegment_099_0162_0010, g32p_row17_traceSegment_099_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 182 10 10, g32p_row17_traceSegment_099_0182_0010, g32p_row17_traceSegment_099_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 162 20 20, g32p_row17_traceSegment_099_0162_0020, g32p_row17_traceSegment_099_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 202 10 10, g32p_row17_traceSegment_099_0202_0010, g32p_row17_traceSegment_099_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 222 10 11, g32p_row17_traceSegment_099_0222_0010, g32p_row17_traceSegment_099_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 202 20 21, g32p_row17_traceSegment_099_0202_0020, g32p_row17_traceSegment_099_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 162 40 41, g32p_row17_traceSegment_099_0162_0040, g32p_row17_traceSegment_099_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 243 10 10, g32p_row17_traceSegment_099_0243_0010, g32p_row17_traceSegment_099_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 263 10 10, g32p_row17_traceSegment_099_0263_0010, g32p_row17_traceSegment_099_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 243 20 20, g32p_row17_traceSegment_099_0243_0020, g32p_row17_traceSegment_099_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 283 10 10, g32p_row17_traceSegment_099_0283_0010, g32p_row17_traceSegment_099_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 303 10 11, g32p_row17_traceSegment_099_0303_0010, g32p_row17_traceSegment_099_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 283 20 21, g32p_row17_traceSegment_099_0283_0020, g32p_row17_traceSegment_099_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 243 40 41, g32p_row17_traceSegment_099_0243_0040, g32p_row17_traceSegment_099_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_099 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 162 81 81, g32p_row17_traceSegment_099_0162_0081, g32p_row17_traceSegment_099_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_099 0 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 0 162 162, g32p_row17_traceSegment_099_0000_0162, g32p_row17_traceSegment_099_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 324 10 10, g32p_row17_traceSegment_099_0324_0010, g32p_row17_traceSegment_099_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 344 10 10, g32p_row17_traceSegment_099_0344_0010, g32p_row17_traceSegment_099_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 324 20 20, g32p_row17_traceSegment_099_0324_0020, g32p_row17_traceSegment_099_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 364 10 10, g32p_row17_traceSegment_099_0364_0010, g32p_row17_traceSegment_099_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 384 10 11, g32p_row17_traceSegment_099_0384_0010, g32p_row17_traceSegment_099_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 364 20 21, g32p_row17_traceSegment_099_0364_0020, g32p_row17_traceSegment_099_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 324 40 41, g32p_row17_traceSegment_099_0324_0040, g32p_row17_traceSegment_099_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 405 10 10, g32p_row17_traceSegment_099_0405_0010, g32p_row17_traceSegment_099_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 425 10 10, g32p_row17_traceSegment_099_0425_0010, g32p_row17_traceSegment_099_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 405 20 20, g32p_row17_traceSegment_099_0405_0020, g32p_row17_traceSegment_099_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 445 10 10, g32p_row17_traceSegment_099_0445_0010, g32p_row17_traceSegment_099_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 465 10 11, g32p_row17_traceSegment_099_0465_0010, g32p_row17_traceSegment_099_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 445 20 21, g32p_row17_traceSegment_099_0445_0020, g32p_row17_traceSegment_099_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 405 40 41, g32p_row17_traceSegment_099_0405_0040, g32p_row17_traceSegment_099_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_099 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 324 81 81, g32p_row17_traceSegment_099_0324_0081, g32p_row17_traceSegment_099_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 486 10 10, g32p_row17_traceSegment_099_0486_0010, g32p_row17_traceSegment_099_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 506 10 10, g32p_row17_traceSegment_099_0506_0010, g32p_row17_traceSegment_099_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 486 20 20, g32p_row17_traceSegment_099_0486_0020, g32p_row17_traceSegment_099_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 526 10 10, g32p_row17_traceSegment_099_0526_0010, g32p_row17_traceSegment_099_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 546 10 11, g32p_row17_traceSegment_099_0546_0010, g32p_row17_traceSegment_099_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 526 20 21, g32p_row17_traceSegment_099_0526_0020, g32p_row17_traceSegment_099_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 486 40 41, g32p_row17_traceSegment_099_0486_0040, g32p_row17_traceSegment_099_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 567 10 10, g32p_row17_traceSegment_099_0567_0010, g32p_row17_traceSegment_099_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 587 10 10, g32p_row17_traceSegment_099_0587_0010, g32p_row17_traceSegment_099_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 567 20 20, g32p_row17_traceSegment_099_0567_0020, g32p_row17_traceSegment_099_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 607 10 10, g32p_row17_traceSegment_099_0607_0010, g32p_row17_traceSegment_099_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 627 10 11, g32p_row17_traceSegment_099_0627_0010, g32p_row17_traceSegment_099_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 607 20 21, g32p_row17_traceSegment_099_0607_0020, g32p_row17_traceSegment_099_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 567 40 41, g32p_row17_traceSegment_099_0567_0040, g32p_row17_traceSegment_099_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_099 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 486 81 81, g32p_row17_traceSegment_099_0486_0081, g32p_row17_traceSegment_099_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_099 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 324 162 162, g32p_row17_traceSegment_099_0324_0162, g32p_row17_traceSegment_099_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_099 0 648 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 0 324 324, g32p_row17_traceSegment_099_0000_0324, g32p_row17_traceSegment_099_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 648 10 10, g32p_row17_traceSegment_099_0648_0010, g32p_row17_traceSegment_099_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 668 10 10, g32p_row17_traceSegment_099_0668_0010, g32p_row17_traceSegment_099_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 648 20 20, g32p_row17_traceSegment_099_0648_0020, g32p_row17_traceSegment_099_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 688 10 10, g32p_row17_traceSegment_099_0688_0010, g32p_row17_traceSegment_099_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 708 10 11, g32p_row17_traceSegment_099_0708_0010, g32p_row17_traceSegment_099_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 688 20 21, g32p_row17_traceSegment_099_0688_0020, g32p_row17_traceSegment_099_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 648 40 41, g32p_row17_traceSegment_099_0648_0040, g32p_row17_traceSegment_099_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 729 10 10, g32p_row17_traceSegment_099_0729_0010, g32p_row17_traceSegment_099_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 749 10 10, g32p_row17_traceSegment_099_0749_0010, g32p_row17_traceSegment_099_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 729 20 20, g32p_row17_traceSegment_099_0729_0020, g32p_row17_traceSegment_099_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 769 10 10, g32p_row17_traceSegment_099_0769_0010, g32p_row17_traceSegment_099_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 789 10 11, g32p_row17_traceSegment_099_0789_0010, g32p_row17_traceSegment_099_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 769 20 21, g32p_row17_traceSegment_099_0769_0020, g32p_row17_traceSegment_099_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 729 40 41, g32p_row17_traceSegment_099_0729_0040, g32p_row17_traceSegment_099_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_099 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 648 81 81, g32p_row17_traceSegment_099_0648_0081, g32p_row17_traceSegment_099_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 810 10 10, g32p_row17_traceSegment_099_0810_0010, g32p_row17_traceSegment_099_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 830 10 10, g32p_row17_traceSegment_099_0830_0010, g32p_row17_traceSegment_099_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 810 20 20, g32p_row17_traceSegment_099_0810_0020, g32p_row17_traceSegment_099_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 850 10 10, g32p_row17_traceSegment_099_0850_0010, g32p_row17_traceSegment_099_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 870 10 11, g32p_row17_traceSegment_099_0870_0010, g32p_row17_traceSegment_099_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 850 20 21, g32p_row17_traceSegment_099_0850_0020, g32p_row17_traceSegment_099_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 810 40 41, g32p_row17_traceSegment_099_0810_0040, g32p_row17_traceSegment_099_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 891 10 10, g32p_row17_traceSegment_099_0891_0010, g32p_row17_traceSegment_099_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 911 10 10, g32p_row17_traceSegment_099_0911_0010, g32p_row17_traceSegment_099_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 891 20 20, g32p_row17_traceSegment_099_0891_0020, g32p_row17_traceSegment_099_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 931 10 10, g32p_row17_traceSegment_099_0931_0010, g32p_row17_traceSegment_099_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 951 10 11, g32p_row17_traceSegment_099_0951_0010, g32p_row17_traceSegment_099_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 931 20 21, g32p_row17_traceSegment_099_0931_0020, g32p_row17_traceSegment_099_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 891 40 41, g32p_row17_traceSegment_099_0891_0040, g32p_row17_traceSegment_099_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_099 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 810 81 81, g32p_row17_traceSegment_099_0810_0081, g32p_row17_traceSegment_099_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_099 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 648 162 162, g32p_row17_traceSegment_099_0648_0162, g32p_row17_traceSegment_099_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 972 10 10, g32p_row17_traceSegment_099_0972_0010, g32p_row17_traceSegment_099_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 992 10 10, g32p_row17_traceSegment_099_0992_0010, g32p_row17_traceSegment_099_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 972 20 20, g32p_row17_traceSegment_099_0972_0020, g32p_row17_traceSegment_099_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1012 10 10, g32p_row17_traceSegment_099_1012_0010, g32p_row17_traceSegment_099_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1032 10 11, g32p_row17_traceSegment_099_1032_0010, g32p_row17_traceSegment_099_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1012 20 21, g32p_row17_traceSegment_099_1012_0020, g32p_row17_traceSegment_099_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 972 40 41, g32p_row17_traceSegment_099_0972_0040, g32p_row17_traceSegment_099_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1053 10 10, g32p_row17_traceSegment_099_1053_0010, g32p_row17_traceSegment_099_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1073 10 10, g32p_row17_traceSegment_099_1073_0010, g32p_row17_traceSegment_099_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1053 20 20, g32p_row17_traceSegment_099_1053_0020, g32p_row17_traceSegment_099_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1093 10 10, g32p_row17_traceSegment_099_1093_0010, g32p_row17_traceSegment_099_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1113 10 11, g32p_row17_traceSegment_099_1113_0010, g32p_row17_traceSegment_099_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1093 20 21, g32p_row17_traceSegment_099_1093_0020, g32p_row17_traceSegment_099_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1053 40 41, g32p_row17_traceSegment_099_1053_0040, g32p_row17_traceSegment_099_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_099 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 972 81 81, g32p_row17_traceSegment_099_0972_0081, g32p_row17_traceSegment_099_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1134 10 10, g32p_row17_traceSegment_099_1134_0010, g32p_row17_traceSegment_099_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1154 10 10, g32p_row17_traceSegment_099_1154_0010, g32p_row17_traceSegment_099_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1134 20 20, g32p_row17_traceSegment_099_1134_0020, g32p_row17_traceSegment_099_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1174 10 10, g32p_row17_traceSegment_099_1174_0010, g32p_row17_traceSegment_099_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1194 10 11, g32p_row17_traceSegment_099_1194_0010, g32p_row17_traceSegment_099_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1174 20 21, g32p_row17_traceSegment_099_1174_0020, g32p_row17_traceSegment_099_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1134 40 41, g32p_row17_traceSegment_099_1134_0040, g32p_row17_traceSegment_099_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1215 10 10, g32p_row17_traceSegment_099_1215_0010, g32p_row17_traceSegment_099_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1235 10 10, g32p_row17_traceSegment_099_1235_0010, g32p_row17_traceSegment_099_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_099 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1215 20 20, g32p_row17_traceSegment_099_1215_0020, g32p_row17_traceSegment_099_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_099 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1255 10 10, g32p_row17_traceSegment_099_1255_0010, g32p_row17_traceSegment_099_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_099 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_099 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_099_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_099 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1275 10 11, g32p_row17_traceSegment_099_1275_0010, g32p_row17_traceSegment_099_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_099 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1255 20 21, g32p_row17_traceSegment_099_1255_0020, g32p_row17_traceSegment_099_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_099 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1215 40 41, g32p_row17_traceSegment_099_1215_0040, g32p_row17_traceSegment_099_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_099_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_099 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 1134 81 81, g32p_row17_traceSegment_099_1134_0081, g32p_row17_traceSegment_099_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_099 972 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 972 162 162, g32p_row17_traceSegment_099_0972_0162, g32p_row17_traceSegment_099_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_099 648 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 648 324 324, g32p_row17_traceSegment_099_0648_0324, g32p_row17_traceSegment_099_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_099_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_099 0 1296 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_099 0 648 648, g32p_row17_traceSegment_099_0000_0648, g32p_row17_traceSegment_099_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 99 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_099_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_tracePolynomial_091 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 91) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 91) (g32p_literalTraceValue 16 91)
      [1, -1, 1] [5184, 5184, 5184] = true := by
  rw [g32p_row17_traceCoefficients_091]
  decide +kernel

theorem g32p_row17_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 92) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 92) (g32p_literalTraceValue 16 92)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row17_traceCoefficients_092]
  decide +kernel

theorem g32p_row17_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 93) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 93) (g32p_literalTraceValue 16 93)
      [1, -1, 1] [15552, 15552, 15552] = true := by
  rw [g32p_row17_traceCoefficients_093]
  decide +kernel

theorem g32p_row17_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 95) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 95) (g32p_literalTraceValue 16 95)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_095]
  decide +kernel

theorem g32p_row17_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 96) (g32p_literalTraceValue 16 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_096]
  decide +kernel

theorem g32p_row17_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 97) (g32p_literalTraceValue 16 97)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_097]
  decide +kernel

theorem g32p_row17_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 98) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 98) (g32p_literalTraceValue 16 98)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_098]
  decide +kernel

theorem g32p_row17_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 99) (g32p_literalTraceValue 16 99)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_099]
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

private def g32p_row17_traceSegment_100 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 100 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_100_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 0 10 10, g32p_row17_traceSegment_100_0000_0010, g32p_row17_traceSegment_100_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 20 10 10, g32p_row17_traceSegment_100_0020_0010, g32p_row17_traceSegment_100_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 0 20 20, g32p_row17_traceSegment_100_0000_0020, g32p_row17_traceSegment_100_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 50 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 40 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 40 10 10, g32p_row17_traceSegment_100_0040_0010, g32p_row17_traceSegment_100_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 60 10 11, g32p_row17_traceSegment_100_0060_0010, g32p_row17_traceSegment_100_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 40 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 40 20 21, g32p_row17_traceSegment_100_0040_0020, g32p_row17_traceSegment_100_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 0 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 0 40 41, g32p_row17_traceSegment_100_0000_0040, g32p_row17_traceSegment_100_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 81 10 10, g32p_row17_traceSegment_100_0081_0010, g32p_row17_traceSegment_100_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 101 10 10, g32p_row17_traceSegment_100_0101_0010, g32p_row17_traceSegment_100_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 81 20 20, g32p_row17_traceSegment_100_0081_0020, g32p_row17_traceSegment_100_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 121 10 10, g32p_row17_traceSegment_100_0121_0010, g32p_row17_traceSegment_100_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 141 10 11, g32p_row17_traceSegment_100_0141_0010, g32p_row17_traceSegment_100_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 121 20 21, g32p_row17_traceSegment_100_0121_0020, g32p_row17_traceSegment_100_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 81 40 41, g32p_row17_traceSegment_100_0081_0040, g32p_row17_traceSegment_100_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_100 0 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 0 81 81, g32p_row17_traceSegment_100_0000_0081, g32p_row17_traceSegment_100_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 162 10 10, g32p_row17_traceSegment_100_0162_0010, g32p_row17_traceSegment_100_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 182 10 10, g32p_row17_traceSegment_100_0182_0010, g32p_row17_traceSegment_100_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 162 20 20, g32p_row17_traceSegment_100_0162_0020, g32p_row17_traceSegment_100_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 202 10 10, g32p_row17_traceSegment_100_0202_0010, g32p_row17_traceSegment_100_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 222 10 11, g32p_row17_traceSegment_100_0222_0010, g32p_row17_traceSegment_100_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 202 20 21, g32p_row17_traceSegment_100_0202_0020, g32p_row17_traceSegment_100_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 162 40 41, g32p_row17_traceSegment_100_0162_0040, g32p_row17_traceSegment_100_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 243 10 10, g32p_row17_traceSegment_100_0243_0010, g32p_row17_traceSegment_100_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 263 10 10, g32p_row17_traceSegment_100_0263_0010, g32p_row17_traceSegment_100_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 243 20 20, g32p_row17_traceSegment_100_0243_0020, g32p_row17_traceSegment_100_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 283 10 10, g32p_row17_traceSegment_100_0283_0010, g32p_row17_traceSegment_100_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 303 10 11, g32p_row17_traceSegment_100_0303_0010, g32p_row17_traceSegment_100_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 283 20 21, g32p_row17_traceSegment_100_0283_0020, g32p_row17_traceSegment_100_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 243 40 41, g32p_row17_traceSegment_100_0243_0040, g32p_row17_traceSegment_100_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_100 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 162 81 81, g32p_row17_traceSegment_100_0162_0081, g32p_row17_traceSegment_100_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_100 0 324 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 0 162 162, g32p_row17_traceSegment_100_0000_0162, g32p_row17_traceSegment_100_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 324 10 10, g32p_row17_traceSegment_100_0324_0010, g32p_row17_traceSegment_100_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 344 10 10, g32p_row17_traceSegment_100_0344_0010, g32p_row17_traceSegment_100_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 324 20 20, g32p_row17_traceSegment_100_0324_0020, g32p_row17_traceSegment_100_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 364 10 10, g32p_row17_traceSegment_100_0364_0010, g32p_row17_traceSegment_100_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 384 10 11, g32p_row17_traceSegment_100_0384_0010, g32p_row17_traceSegment_100_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 364 20 21, g32p_row17_traceSegment_100_0364_0020, g32p_row17_traceSegment_100_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 324 40 41, g32p_row17_traceSegment_100_0324_0040, g32p_row17_traceSegment_100_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 405 10 10, g32p_row17_traceSegment_100_0405_0010, g32p_row17_traceSegment_100_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 425 10 10, g32p_row17_traceSegment_100_0425_0010, g32p_row17_traceSegment_100_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 405 20 20, g32p_row17_traceSegment_100_0405_0020, g32p_row17_traceSegment_100_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 445 10 10, g32p_row17_traceSegment_100_0445_0010, g32p_row17_traceSegment_100_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 465 10 11, g32p_row17_traceSegment_100_0465_0010, g32p_row17_traceSegment_100_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 445 20 21, g32p_row17_traceSegment_100_0445_0020, g32p_row17_traceSegment_100_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 405 40 41, g32p_row17_traceSegment_100_0405_0040, g32p_row17_traceSegment_100_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_100 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 324 81 81, g32p_row17_traceSegment_100_0324_0081, g32p_row17_traceSegment_100_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 486 10 10, g32p_row17_traceSegment_100_0486_0010, g32p_row17_traceSegment_100_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 506 10 10, g32p_row17_traceSegment_100_0506_0010, g32p_row17_traceSegment_100_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 486 20 20, g32p_row17_traceSegment_100_0486_0020, g32p_row17_traceSegment_100_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 526 10 10, g32p_row17_traceSegment_100_0526_0010, g32p_row17_traceSegment_100_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 546 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 546 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 546 10 11, g32p_row17_traceSegment_100_0546_0010, g32p_row17_traceSegment_100_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 526 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 526 20 21, g32p_row17_traceSegment_100_0526_0020, g32p_row17_traceSegment_100_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 486 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 486 40 41, g32p_row17_traceSegment_100_0486_0040, g32p_row17_traceSegment_100_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 567 10 10, g32p_row17_traceSegment_100_0567_0010, g32p_row17_traceSegment_100_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 587 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 587 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 587 10 10, g32p_row17_traceSegment_100_0587_0010, g32p_row17_traceSegment_100_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 567 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 567 20 20, g32p_row17_traceSegment_100_0567_0020, g32p_row17_traceSegment_100_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 607 10 10, g32p_row17_traceSegment_100_0607_0010, g32p_row17_traceSegment_100_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 627 10 11, g32p_row17_traceSegment_100_0627_0010, g32p_row17_traceSegment_100_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 607 20 21, g32p_row17_traceSegment_100_0607_0020, g32p_row17_traceSegment_100_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 567 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 567 40 41, g32p_row17_traceSegment_100_0567_0040, g32p_row17_traceSegment_100_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_100 486 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 486 81 81, g32p_row17_traceSegment_100_0486_0081, g32p_row17_traceSegment_100_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_100 324 324 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 324 162 162, g32p_row17_traceSegment_100_0324_0162, g32p_row17_traceSegment_100_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_100 0 648 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 0 324 324, g32p_row17_traceSegment_100_0000_0324, g32p_row17_traceSegment_100_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 648 10 10, g32p_row17_traceSegment_100_0648_0010, g32p_row17_traceSegment_100_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 668 10 10, g32p_row17_traceSegment_100_0668_0010, g32p_row17_traceSegment_100_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 648 20 20, g32p_row17_traceSegment_100_0648_0020, g32p_row17_traceSegment_100_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 688 10 10, g32p_row17_traceSegment_100_0688_0010, g32p_row17_traceSegment_100_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 708 10 11, g32p_row17_traceSegment_100_0708_0010, g32p_row17_traceSegment_100_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 688 20 21, g32p_row17_traceSegment_100_0688_0020, g32p_row17_traceSegment_100_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 648 40 41, g32p_row17_traceSegment_100_0648_0040, g32p_row17_traceSegment_100_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 739 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 729 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 729 10 10, g32p_row17_traceSegment_100_0729_0010, g32p_row17_traceSegment_100_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 749 10 10, g32p_row17_traceSegment_100_0749_0010, g32p_row17_traceSegment_100_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 729 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 729 20 20, g32p_row17_traceSegment_100_0729_0020, g32p_row17_traceSegment_100_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 769 10 10, g32p_row17_traceSegment_100_0769_0010, g32p_row17_traceSegment_100_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 789 10 11, g32p_row17_traceSegment_100_0789_0010, g32p_row17_traceSegment_100_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 769 20 21, g32p_row17_traceSegment_100_0769_0020, g32p_row17_traceSegment_100_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 729 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 729 40 41, g32p_row17_traceSegment_100_0729_0040, g32p_row17_traceSegment_100_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_100 648 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 648 81 81, g32p_row17_traceSegment_100_0648_0081, g32p_row17_traceSegment_100_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 810 10 10, g32p_row17_traceSegment_100_0810_0010, g32p_row17_traceSegment_100_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 830 10 10, g32p_row17_traceSegment_100_0830_0010, g32p_row17_traceSegment_100_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 810 20 20, g32p_row17_traceSegment_100_0810_0020, g32p_row17_traceSegment_100_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 850 10 10, g32p_row17_traceSegment_100_0850_0010, g32p_row17_traceSegment_100_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 870 10 11, g32p_row17_traceSegment_100_0870_0010, g32p_row17_traceSegment_100_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 850 20 21, g32p_row17_traceSegment_100_0850_0020, g32p_row17_traceSegment_100_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 810 40 41, g32p_row17_traceSegment_100_0810_0040, g32p_row17_traceSegment_100_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 891 10 10, g32p_row17_traceSegment_100_0891_0010, g32p_row17_traceSegment_100_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 911 10 10, g32p_row17_traceSegment_100_0911_0010, g32p_row17_traceSegment_100_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 891 20 20, g32p_row17_traceSegment_100_0891_0020, g32p_row17_traceSegment_100_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 931 10 10, g32p_row17_traceSegment_100_0931_0010, g32p_row17_traceSegment_100_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 951 10 11, g32p_row17_traceSegment_100_0951_0010, g32p_row17_traceSegment_100_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 931 20 21, g32p_row17_traceSegment_100_0931_0020, g32p_row17_traceSegment_100_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 891 40 41, g32p_row17_traceSegment_100_0891_0040, g32p_row17_traceSegment_100_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_100 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 810 81 81, g32p_row17_traceSegment_100_0810_0081, g32p_row17_traceSegment_100_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_100 648 324 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 648 162 162, g32p_row17_traceSegment_100_0648_0162, g32p_row17_traceSegment_100_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 972 10 10, g32p_row17_traceSegment_100_0972_0010, g32p_row17_traceSegment_100_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 992 10 10, g32p_row17_traceSegment_100_0992_0010, g32p_row17_traceSegment_100_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 972 20 20, g32p_row17_traceSegment_100_0972_0020, g32p_row17_traceSegment_100_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1012 10 10, g32p_row17_traceSegment_100_1012_0010, g32p_row17_traceSegment_100_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1032 10 11, g32p_row17_traceSegment_100_1032_0010, g32p_row17_traceSegment_100_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1012 20 21, g32p_row17_traceSegment_100_1012_0020, g32p_row17_traceSegment_100_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 972 40 41, g32p_row17_traceSegment_100_0972_0040, g32p_row17_traceSegment_100_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1053 10 10, g32p_row17_traceSegment_100_1053_0010, g32p_row17_traceSegment_100_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1073 10 10, g32p_row17_traceSegment_100_1073_0010, g32p_row17_traceSegment_100_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1053 20 20, g32p_row17_traceSegment_100_1053_0020, g32p_row17_traceSegment_100_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1093 10 10, g32p_row17_traceSegment_100_1093_0010, g32p_row17_traceSegment_100_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1113 10 11, g32p_row17_traceSegment_100_1113_0010, g32p_row17_traceSegment_100_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1093 20 21, g32p_row17_traceSegment_100_1093_0020, g32p_row17_traceSegment_100_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1053 40 41, g32p_row17_traceSegment_100_1053_0040, g32p_row17_traceSegment_100_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_100 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 972 81 81, g32p_row17_traceSegment_100_0972_0081, g32p_row17_traceSegment_100_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1134 10 10, g32p_row17_traceSegment_100_1134_0010, g32p_row17_traceSegment_100_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1154 10 10, g32p_row17_traceSegment_100_1154_0010, g32p_row17_traceSegment_100_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1134 20 20, g32p_row17_traceSegment_100_1134_0020, g32p_row17_traceSegment_100_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1174 10 10, g32p_row17_traceSegment_100_1174_0010, g32p_row17_traceSegment_100_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1194 10 11, g32p_row17_traceSegment_100_1194_0010, g32p_row17_traceSegment_100_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1174 20 21, g32p_row17_traceSegment_100_1174_0020, g32p_row17_traceSegment_100_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1134 40 41, g32p_row17_traceSegment_100_1134_0040, g32p_row17_traceSegment_100_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1215 10 10, g32p_row17_traceSegment_100_1215_0010, g32p_row17_traceSegment_100_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1235 10 10, g32p_row17_traceSegment_100_1235_0010, g32p_row17_traceSegment_100_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_100 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1215 20 20, g32p_row17_traceSegment_100_1215_0020, g32p_row17_traceSegment_100_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_100 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1255 10 10, g32p_row17_traceSegment_100_1255_0010, g32p_row17_traceSegment_100_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_100 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_100 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_100_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_100 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1275 10 11, g32p_row17_traceSegment_100_1275_0010, g32p_row17_traceSegment_100_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_100 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1255 20 21, g32p_row17_traceSegment_100_1255_0020, g32p_row17_traceSegment_100_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_100 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1215 40 41, g32p_row17_traceSegment_100_1215_0040, g32p_row17_traceSegment_100_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_100_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_100 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 1134 81 81, g32p_row17_traceSegment_100_1134_0081, g32p_row17_traceSegment_100_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_100 972 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 972 162 162, g32p_row17_traceSegment_100_0972_0162, g32p_row17_traceSegment_100_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_100 648 648 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 648 324 324, g32p_row17_traceSegment_100_0648_0324, g32p_row17_traceSegment_100_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_100_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_100 0 1296 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_100 0 648 648, g32p_row17_traceSegment_100_0000_0648, g32p_row17_traceSegment_100_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 100 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_100_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_101 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 101 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_101_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 0 10 10, g32p_row17_traceSegment_101_0000_0010, g32p_row17_traceSegment_101_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 20 10 10, g32p_row17_traceSegment_101_0020_0010, g32p_row17_traceSegment_101_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 0 20 20, g32p_row17_traceSegment_101_0000_0020, g32p_row17_traceSegment_101_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 40 10 10, g32p_row17_traceSegment_101_0040_0010, g32p_row17_traceSegment_101_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 60 10 11, g32p_row17_traceSegment_101_0060_0010, g32p_row17_traceSegment_101_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 40 20 21, g32p_row17_traceSegment_101_0040_0020, g32p_row17_traceSegment_101_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 0 40 41, g32p_row17_traceSegment_101_0000_0040, g32p_row17_traceSegment_101_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 81 10 10, g32p_row17_traceSegment_101_0081_0010, g32p_row17_traceSegment_101_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 101 10 10, g32p_row17_traceSegment_101_0101_0010, g32p_row17_traceSegment_101_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 81 20 20, g32p_row17_traceSegment_101_0081_0020, g32p_row17_traceSegment_101_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 121 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 121 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 121 10 10, g32p_row17_traceSegment_101_0121_0010, g32p_row17_traceSegment_101_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 141 10 11, g32p_row17_traceSegment_101_0141_0010, g32p_row17_traceSegment_101_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 121 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 121 20 21, g32p_row17_traceSegment_101_0121_0020, g32p_row17_traceSegment_101_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 81 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 81 40 41, g32p_row17_traceSegment_101_0081_0040, g32p_row17_traceSegment_101_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_101 0 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 0 81 81, g32p_row17_traceSegment_101_0000_0081, g32p_row17_traceSegment_101_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 162 10 10, g32p_row17_traceSegment_101_0162_0010, g32p_row17_traceSegment_101_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 182 10 10, g32p_row17_traceSegment_101_0182_0010, g32p_row17_traceSegment_101_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 162 20 20, g32p_row17_traceSegment_101_0162_0020, g32p_row17_traceSegment_101_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 202 10 10, g32p_row17_traceSegment_101_0202_0010, g32p_row17_traceSegment_101_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 222 10 11, g32p_row17_traceSegment_101_0222_0010, g32p_row17_traceSegment_101_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 202 20 21, g32p_row17_traceSegment_101_0202_0020, g32p_row17_traceSegment_101_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 162 40 41, g32p_row17_traceSegment_101_0162_0040, g32p_row17_traceSegment_101_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 243 10 10, g32p_row17_traceSegment_101_0243_0010, g32p_row17_traceSegment_101_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 263 10 10, g32p_row17_traceSegment_101_0263_0010, g32p_row17_traceSegment_101_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 243 20 20, g32p_row17_traceSegment_101_0243_0020, g32p_row17_traceSegment_101_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 283 10 10, g32p_row17_traceSegment_101_0283_0010, g32p_row17_traceSegment_101_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 303 10 11, g32p_row17_traceSegment_101_0303_0010, g32p_row17_traceSegment_101_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 283 20 21, g32p_row17_traceSegment_101_0283_0020, g32p_row17_traceSegment_101_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 243 40 41, g32p_row17_traceSegment_101_0243_0040, g32p_row17_traceSegment_101_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_101 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 162 81 81, g32p_row17_traceSegment_101_0162_0081, g32p_row17_traceSegment_101_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_101 0 324 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 0 162 162, g32p_row17_traceSegment_101_0000_0162, g32p_row17_traceSegment_101_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 324 10 10, g32p_row17_traceSegment_101_0324_0010, g32p_row17_traceSegment_101_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 344 10 10, g32p_row17_traceSegment_101_0344_0010, g32p_row17_traceSegment_101_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 324 20 20, g32p_row17_traceSegment_101_0324_0020, g32p_row17_traceSegment_101_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 364 10 10, g32p_row17_traceSegment_101_0364_0010, g32p_row17_traceSegment_101_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 384 10 11, g32p_row17_traceSegment_101_0384_0010, g32p_row17_traceSegment_101_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 364 20 21, g32p_row17_traceSegment_101_0364_0020, g32p_row17_traceSegment_101_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 324 40 41, g32p_row17_traceSegment_101_0324_0040, g32p_row17_traceSegment_101_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 405 10 10, g32p_row17_traceSegment_101_0405_0010, g32p_row17_traceSegment_101_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 425 10 10, g32p_row17_traceSegment_101_0425_0010, g32p_row17_traceSegment_101_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 405 20 20, g32p_row17_traceSegment_101_0405_0020, g32p_row17_traceSegment_101_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 445 10 10, g32p_row17_traceSegment_101_0445_0010, g32p_row17_traceSegment_101_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 465 10 11, g32p_row17_traceSegment_101_0465_0010, g32p_row17_traceSegment_101_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 445 20 21, g32p_row17_traceSegment_101_0445_0020, g32p_row17_traceSegment_101_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 405 40 41, g32p_row17_traceSegment_101_0405_0040, g32p_row17_traceSegment_101_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_101 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 324 81 81, g32p_row17_traceSegment_101_0324_0081, g32p_row17_traceSegment_101_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 486 10 10, g32p_row17_traceSegment_101_0486_0010, g32p_row17_traceSegment_101_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 506 10 10, g32p_row17_traceSegment_101_0506_0010, g32p_row17_traceSegment_101_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 486 20 20, g32p_row17_traceSegment_101_0486_0020, g32p_row17_traceSegment_101_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 526 10 10, g32p_row17_traceSegment_101_0526_0010, g32p_row17_traceSegment_101_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 546 10 11, g32p_row17_traceSegment_101_0546_0010, g32p_row17_traceSegment_101_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 526 20 21, g32p_row17_traceSegment_101_0526_0020, g32p_row17_traceSegment_101_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 486 40 41, g32p_row17_traceSegment_101_0486_0040, g32p_row17_traceSegment_101_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 567 10 10, g32p_row17_traceSegment_101_0567_0010, g32p_row17_traceSegment_101_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 587 10 10, g32p_row17_traceSegment_101_0587_0010, g32p_row17_traceSegment_101_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 567 20 20, g32p_row17_traceSegment_101_0567_0020, g32p_row17_traceSegment_101_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 607 10 10, g32p_row17_traceSegment_101_0607_0010, g32p_row17_traceSegment_101_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 627 10 11, g32p_row17_traceSegment_101_0627_0010, g32p_row17_traceSegment_101_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 607 20 21, g32p_row17_traceSegment_101_0607_0020, g32p_row17_traceSegment_101_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 567 40 41, g32p_row17_traceSegment_101_0567_0040, g32p_row17_traceSegment_101_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_101 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 486 81 81, g32p_row17_traceSegment_101_0486_0081, g32p_row17_traceSegment_101_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_101 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 324 162 162, g32p_row17_traceSegment_101_0324_0162, g32p_row17_traceSegment_101_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_101 0 648 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 0 324 324, g32p_row17_traceSegment_101_0000_0324, g32p_row17_traceSegment_101_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 648 10 10, g32p_row17_traceSegment_101_0648_0010, g32p_row17_traceSegment_101_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 668 10 10, g32p_row17_traceSegment_101_0668_0010, g32p_row17_traceSegment_101_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 648 20 20, g32p_row17_traceSegment_101_0648_0020, g32p_row17_traceSegment_101_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 688 10 10, g32p_row17_traceSegment_101_0688_0010, g32p_row17_traceSegment_101_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 708 10 11, g32p_row17_traceSegment_101_0708_0010, g32p_row17_traceSegment_101_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 688 20 21, g32p_row17_traceSegment_101_0688_0020, g32p_row17_traceSegment_101_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 648 40 41, g32p_row17_traceSegment_101_0648_0040, g32p_row17_traceSegment_101_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 729 10 10, g32p_row17_traceSegment_101_0729_0010, g32p_row17_traceSegment_101_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 749 10 10, g32p_row17_traceSegment_101_0749_0010, g32p_row17_traceSegment_101_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 729 20 20, g32p_row17_traceSegment_101_0729_0020, g32p_row17_traceSegment_101_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 769 10 10, g32p_row17_traceSegment_101_0769_0010, g32p_row17_traceSegment_101_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 789 10 11, g32p_row17_traceSegment_101_0789_0010, g32p_row17_traceSegment_101_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 769 20 21, g32p_row17_traceSegment_101_0769_0020, g32p_row17_traceSegment_101_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 729 40 41, g32p_row17_traceSegment_101_0729_0040, g32p_row17_traceSegment_101_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_101 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 648 81 81, g32p_row17_traceSegment_101_0648_0081, g32p_row17_traceSegment_101_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 810 10 10, g32p_row17_traceSegment_101_0810_0010, g32p_row17_traceSegment_101_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 830 10 10, g32p_row17_traceSegment_101_0830_0010, g32p_row17_traceSegment_101_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 810 20 20, g32p_row17_traceSegment_101_0810_0020, g32p_row17_traceSegment_101_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 850 10 10, g32p_row17_traceSegment_101_0850_0010, g32p_row17_traceSegment_101_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 870 10 11, g32p_row17_traceSegment_101_0870_0010, g32p_row17_traceSegment_101_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 850 20 21, g32p_row17_traceSegment_101_0850_0020, g32p_row17_traceSegment_101_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 810 40 41, g32p_row17_traceSegment_101_0810_0040, g32p_row17_traceSegment_101_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 891 10 10, g32p_row17_traceSegment_101_0891_0010, g32p_row17_traceSegment_101_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 911 10 10, g32p_row17_traceSegment_101_0911_0010, g32p_row17_traceSegment_101_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 891 20 20, g32p_row17_traceSegment_101_0891_0020, g32p_row17_traceSegment_101_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 931 10 10, g32p_row17_traceSegment_101_0931_0010, g32p_row17_traceSegment_101_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 951 10 11, g32p_row17_traceSegment_101_0951_0010, g32p_row17_traceSegment_101_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 931 20 21, g32p_row17_traceSegment_101_0931_0020, g32p_row17_traceSegment_101_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 891 40 41, g32p_row17_traceSegment_101_0891_0040, g32p_row17_traceSegment_101_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_101 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 810 81 81, g32p_row17_traceSegment_101_0810_0081, g32p_row17_traceSegment_101_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_101 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 648 162 162, g32p_row17_traceSegment_101_0648_0162, g32p_row17_traceSegment_101_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 972 10 10, g32p_row17_traceSegment_101_0972_0010, g32p_row17_traceSegment_101_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 992 10 10, g32p_row17_traceSegment_101_0992_0010, g32p_row17_traceSegment_101_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 972 20 20, g32p_row17_traceSegment_101_0972_0020, g32p_row17_traceSegment_101_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1012 10 10, g32p_row17_traceSegment_101_1012_0010, g32p_row17_traceSegment_101_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1032 10 11, g32p_row17_traceSegment_101_1032_0010, g32p_row17_traceSegment_101_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1012 20 21, g32p_row17_traceSegment_101_1012_0020, g32p_row17_traceSegment_101_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 972 40 41, g32p_row17_traceSegment_101_0972_0040, g32p_row17_traceSegment_101_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1053 10 10, g32p_row17_traceSegment_101_1053_0010, g32p_row17_traceSegment_101_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1073 10 10, g32p_row17_traceSegment_101_1073_0010, g32p_row17_traceSegment_101_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1053 20 20, g32p_row17_traceSegment_101_1053_0020, g32p_row17_traceSegment_101_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1093 10 10, g32p_row17_traceSegment_101_1093_0010, g32p_row17_traceSegment_101_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1113 10 11, g32p_row17_traceSegment_101_1113_0010, g32p_row17_traceSegment_101_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1093 20 21, g32p_row17_traceSegment_101_1093_0020, g32p_row17_traceSegment_101_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1053 40 41, g32p_row17_traceSegment_101_1053_0040, g32p_row17_traceSegment_101_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_101 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 972 81 81, g32p_row17_traceSegment_101_0972_0081, g32p_row17_traceSegment_101_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1134 10 10, g32p_row17_traceSegment_101_1134_0010, g32p_row17_traceSegment_101_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1154 10 10, g32p_row17_traceSegment_101_1154_0010, g32p_row17_traceSegment_101_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1134 20 20, g32p_row17_traceSegment_101_1134_0020, g32p_row17_traceSegment_101_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1174 10 10, g32p_row17_traceSegment_101_1174_0010, g32p_row17_traceSegment_101_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1194 10 11, g32p_row17_traceSegment_101_1194_0010, g32p_row17_traceSegment_101_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1174 20 21, g32p_row17_traceSegment_101_1174_0020, g32p_row17_traceSegment_101_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1134 40 41, g32p_row17_traceSegment_101_1134_0040, g32p_row17_traceSegment_101_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1215 10 10, g32p_row17_traceSegment_101_1215_0010, g32p_row17_traceSegment_101_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1235 10 10, g32p_row17_traceSegment_101_1235_0010, g32p_row17_traceSegment_101_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_101 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1215 20 20, g32p_row17_traceSegment_101_1215_0020, g32p_row17_traceSegment_101_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_101 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1255 10 10, g32p_row17_traceSegment_101_1255_0010, g32p_row17_traceSegment_101_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_101 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_101 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_101_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_101 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1275 10 11, g32p_row17_traceSegment_101_1275_0010, g32p_row17_traceSegment_101_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_101 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1255 20 21, g32p_row17_traceSegment_101_1255_0020, g32p_row17_traceSegment_101_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_101 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1215 40 41, g32p_row17_traceSegment_101_1215_0040, g32p_row17_traceSegment_101_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_101_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_101 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 1134 81 81, g32p_row17_traceSegment_101_1134_0081, g32p_row17_traceSegment_101_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_101 972 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 972 162 162, g32p_row17_traceSegment_101_0972_0162, g32p_row17_traceSegment_101_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_101 648 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 648 324 324, g32p_row17_traceSegment_101_0648_0324, g32p_row17_traceSegment_101_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_101_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_101 0 1296 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_101 0 648 648, g32p_row17_traceSegment_101_0000_0648, g32p_row17_traceSegment_101_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 101 = [0, 0, 0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_101_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 100) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 100) (g32p_literalTraceValue 16 100)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_100]
  decide +kernel

theorem g32p_row17_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 101) (g32p_literalTraceValue 16 101)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row17_traceCoefficients_101]
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row17_generatorIndex : Fin 8 → Fin 408 :=
  ![16, 67, 118, 169, 236, 237, 338, 339]

theorem g32p_row17_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup12_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 16 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 16 g32p_row17_supplierClass
    g32p_row17_supplierClass_isConj g32p_supplierGroup12_support g32p_row17_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row17_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup12_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row17_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 16 c false (g32p_row17_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 16 c true (g32p_row17_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 16 c false (g32p_row17_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 16 c true (g32p_row17_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 16 c false (g32p_row17_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 16 c false (g32p_row17_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 16 c true (g32p_row17_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 16 c true (g32p_row17_coinduced_zero c hc true) 3

theorem g32p_row17_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup12_support →
      g32p_literalTraceValue (g32p_row17_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row17_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup12_support →
      g32p_literalTraceValue (g32p_row17_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row17_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup12_support →
      g32p_literalTraceValue (g32p_row17_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row17_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup12_support →
      g32p_literalTraceValue (g32p_row17_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row17_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup12_support →
      g32p_literalTraceValue (g32p_row17_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row17_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup12_support →
      g32p_literalTraceValue (g32p_row17_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row17_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup12_support →
      g32p_literalTraceValue (g32p_row17_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row17_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup12_support) :
    g32p_literalTraceValue (g32p_row17_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup12_support →
    g32p_literalTraceValue (g32p_row17_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row17_zeroTrace_block_00 r k
  · exact g32p_row17_zeroTrace_block_01 r k
  · exact g32p_row17_zeroTrace_block_02 r k
  · exact g32p_row17_zeroTrace_block_03 r k
  · exact g32p_row17_zeroTrace_block_04 r k
  · exact g32p_row17_zeroTrace_block_05 r k
  · exact g32p_row17_zeroTrace_block_06 r k

theorem g32p_row17_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup12_support) :
    (g32p_recordedInductionGenerators (g32p_row17_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row17_generatorIndex k) c) := by
  rw [g32p_row17_recordedGenerator_zero c hc k, g32p_row17_zeroTrace_arithmetic c k hc]
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

def g32p_row17_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [15552, 15552, 15552])) else (if i.val < 4 then [5184, 5184, 5184] else (if i.val < 5 then [3888, 3888, 3888] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [0, 0, 10368, 10368] else [])) else (if i.val < 16 then [1296, 1296, 1296] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [2592, 2592] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [1296, 1296, 1296] else [-1296, 1296, 1296]))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [3888, 3888, 3888] else [])) else (if i.val < 36 then (if i.val < 35 then [-5184, 5184, 5184] else [3888, 3888, 3888]) else (if i.val < 37 then [] else [155520, 155520, 155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [2592, 2592] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [0, 0, 2592, 2592])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [0, 0, 2592, 2592] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [-2592] else (if i.val < 59 then [] else [1296, 1296, 1296])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [5184, 5184, 5184] else [20736, 20736, 20736])) else (if i.val < 67 then [1296, 1296, 1296] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [10368, 10368] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [15552, 15552, 15552] else [15552, 15552, 15552])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [5184, 5184, 5184] else (if i.val < 91 then [] else [5184, 5184, 5184])) else (if i.val < 93 then [3888, 3888, 3888] else (if i.val < 94 then [15552, 15552, 15552] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [155520, 155520, 155520])))))))

theorem g32p_row17_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup12_support) :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) c) (g32p_literalTraceValue 16 c)
      [1, -1, 1] (g32p_row17_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row17_tracePolynomial_000
  · exact g32p_row17_tracePolynomial_001
  · exact g32p_row17_tracePolynomial_002
  · exact g32p_row17_tracePolynomial_003
  · exact g32p_row17_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_008
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_010
  · exact g32p_row17_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_018
  · exact g32p_row17_tracePolynomial_019
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_021
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_023
  · exact g32p_row17_tracePolynomial_024
  · exact g32p_row17_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_028
  · exact g32p_row17_tracePolynomial_029
  · exact g32p_row17_tracePolynomial_030
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_034
  · exact g32p_row17_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_037
  · exact g32p_row17_tracePolynomial_038
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_040
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_043
  · exact g32p_row17_tracePolynomial_044
  · exact g32p_row17_tracePolynomial_045
  · exact g32p_row17_tracePolynomial_046
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_049
  · exact g32p_row17_tracePolynomial_050
  · exact g32p_row17_tracePolynomial_051
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_056
  · exact g32p_row17_tracePolynomial_057
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_064
  · exact g32p_row17_tracePolynomial_065
  · exact g32p_row17_tracePolynomial_066
  · exact g32p_row17_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_071
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_074
  · exact g32p_row17_tracePolynomial_075
  · exact g32p_row17_tracePolynomial_076
  · exact g32p_row17_tracePolynomial_077
  · exact g32p_row17_tracePolynomial_078
  · exact g32p_row17_tracePolynomial_079
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_081
  · exact g32p_row17_tracePolynomial_082
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_084
  · exact g32p_row17_tracePolynomial_085
  · exact g32p_row17_tracePolynomial_086
  · exact g32p_row17_tracePolynomial_087
  · exact g32p_row17_tracePolynomial_088
  · exact g32p_row17_tracePolynomial_089
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_091
  · exact g32p_row17_tracePolynomial_092
  · exact g32p_row17_tracePolynomial_093
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup12_support) hc)
  · exact g32p_row17_tracePolynomial_095
  · exact g32p_row17_tracePolynomial_096
  · exact g32p_row17_tracePolynomial_097
  · exact g32p_row17_tracePolynomial_098
  · exact g32p_row17_tracePolynomial_099
  · exact g32p_row17_tracePolynomial_100
  · exact g32p_row17_tracePolynomial_101

theorem g32p_row17_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 16 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 16 c) := by
  by_cases hc : c ∈ g32p_supplierGroup12_support
  · have hclass (j : Fin 1296) :
        IsConj (g32p_literalRepresentative c) (g32p_row17_groupEquiv j : g32p_G) ↔
          g32p_row17_supplierClassifier j = c := by
      simpa only [g32p_row17_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row17_supplierClass_iff (g32p_row17_groupEquiv j) c
    have hχ (j : Fin 1296) :
        (g32p_recordedSupplierCharacters 16 (g32p_row17_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row17_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 16 (show (g32p_recordedSuppliers 16).H from g32p_row17_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row17_characterValues (g32p_row17_groupEquiv.symm (g32p_row17_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 16).H (g32p_recordedSupplierCharacters 16)
      (g32p_literalRepresentative c) g32p_row17_groupEquiv g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) c 6 1296
      (g32p_literalCentralizer c) (g32p_literalTraceValue 16 c) [1, -1, 1]
      (g32p_row17_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row17_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 16)))
      (g32p_row17_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row17_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
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

theorem g32p_row17_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
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

theorem g32p_row17_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
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

theorem g32p_row17_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
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

theorem g32p_row17_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
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

theorem g32p_row17_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row17_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row17_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 16 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
