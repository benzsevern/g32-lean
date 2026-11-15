import HodgeLean.Foundations.Program.G32PropFourSixPacked0354
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0355
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row08_traceSegment_092 (k : ℕ) : List ℤ :=
  if g32p_row08_supplierClassifier (Fin.ofNat 648 k) = 92 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row08_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row08_traceSegment_092_0000_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 0 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0010_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 10 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0000_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 0 10 10, g32p_row08_traceSegment_092_0000_0010, g32p_row08_traceSegment_092_0010_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0020_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 20 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0030_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 30 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0020_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 20 10 10, g32p_row08_traceSegment_092_0020_0010, g32p_row08_traceSegment_092_0030_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0000_0040 : g32p_coeffSegment g32p_row08_traceSegment_092 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 0 20 20, g32p_row08_traceSegment_092_0000_0020, g32p_row08_traceSegment_092_0020_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0040_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 40 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0050_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 50 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0040_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 40 10 10, g32p_row08_traceSegment_092_0040_0010, g32p_row08_traceSegment_092_0050_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0060_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 60 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0070_0011 : g32p_coeffSegment g32p_row08_traceSegment_092 70 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0060_0021 : g32p_coeffSegment g32p_row08_traceSegment_092 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 60 10 11, g32p_row08_traceSegment_092_0060_0010, g32p_row08_traceSegment_092_0070_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0040_0041 : g32p_coeffSegment g32p_row08_traceSegment_092 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 40 20 21, g32p_row08_traceSegment_092_0040_0020, g32p_row08_traceSegment_092_0060_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0000_0081 : g32p_coeffSegment g32p_row08_traceSegment_092 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 0 40 41, g32p_row08_traceSegment_092_0000_0040, g32p_row08_traceSegment_092_0040_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0081_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 81 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0091_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 91 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0081_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 81 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 81 10 10, g32p_row08_traceSegment_092_0081_0010, g32p_row08_traceSegment_092_0091_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0101_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 101 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0111_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 111 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0101_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 101 10 10, g32p_row08_traceSegment_092_0101_0010, g32p_row08_traceSegment_092_0111_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0081_0040 : g32p_coeffSegment g32p_row08_traceSegment_092 81 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 81 20 20, g32p_row08_traceSegment_092_0081_0020, g32p_row08_traceSegment_092_0101_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0121_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 121 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0131_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 131 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0121_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 121 10 10, g32p_row08_traceSegment_092_0121_0010, g32p_row08_traceSegment_092_0131_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0141_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 141 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0151_0011 : g32p_coeffSegment g32p_row08_traceSegment_092 151 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0141_0021 : g32p_coeffSegment g32p_row08_traceSegment_092 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 141 10 11, g32p_row08_traceSegment_092_0141_0010, g32p_row08_traceSegment_092_0151_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0121_0041 : g32p_coeffSegment g32p_row08_traceSegment_092 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 121 20 21, g32p_row08_traceSegment_092_0121_0020, g32p_row08_traceSegment_092_0141_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0081_0081 : g32p_coeffSegment g32p_row08_traceSegment_092 81 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 81 40 41, g32p_row08_traceSegment_092_0081_0040, g32p_row08_traceSegment_092_0121_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0000_0162 : g32p_coeffSegment g32p_row08_traceSegment_092 0 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 0 81 81, g32p_row08_traceSegment_092_0000_0081, g32p_row08_traceSegment_092_0081_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0162_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 162 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0172_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 172 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0162_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 162 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 162 10 10, g32p_row08_traceSegment_092_0162_0010, g32p_row08_traceSegment_092_0172_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0182_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 182 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0192_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 192 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0182_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 182 10 10, g32p_row08_traceSegment_092_0182_0010, g32p_row08_traceSegment_092_0192_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0162_0040 : g32p_coeffSegment g32p_row08_traceSegment_092 162 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 162 20 20, g32p_row08_traceSegment_092_0162_0020, g32p_row08_traceSegment_092_0182_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0202_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 202 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0212_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 212 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0202_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 202 10 10, g32p_row08_traceSegment_092_0202_0010, g32p_row08_traceSegment_092_0212_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0222_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 222 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0232_0011 : g32p_coeffSegment g32p_row08_traceSegment_092 232 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0222_0021 : g32p_coeffSegment g32p_row08_traceSegment_092 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 222 10 11, g32p_row08_traceSegment_092_0222_0010, g32p_row08_traceSegment_092_0232_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0202_0041 : g32p_coeffSegment g32p_row08_traceSegment_092 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 202 20 21, g32p_row08_traceSegment_092_0202_0020, g32p_row08_traceSegment_092_0222_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0162_0081 : g32p_coeffSegment g32p_row08_traceSegment_092 162 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 162 40 41, g32p_row08_traceSegment_092_0162_0040, g32p_row08_traceSegment_092_0202_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0243_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 243 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0253_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 253 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0243_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 243 10 10, g32p_row08_traceSegment_092_0243_0010, g32p_row08_traceSegment_092_0253_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0263_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 263 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0273_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 273 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0263_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 263 10 10, g32p_row08_traceSegment_092_0263_0010, g32p_row08_traceSegment_092_0273_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0243_0040 : g32p_coeffSegment g32p_row08_traceSegment_092 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 243 20 20, g32p_row08_traceSegment_092_0243_0020, g32p_row08_traceSegment_092_0263_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0283_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 283 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0293_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 293 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0283_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 283 10 10, g32p_row08_traceSegment_092_0283_0010, g32p_row08_traceSegment_092_0293_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0303_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 303 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0313_0011 : g32p_coeffSegment g32p_row08_traceSegment_092 313 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0303_0021 : g32p_coeffSegment g32p_row08_traceSegment_092 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 303 10 11, g32p_row08_traceSegment_092_0303_0010, g32p_row08_traceSegment_092_0313_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0283_0041 : g32p_coeffSegment g32p_row08_traceSegment_092 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 283 20 21, g32p_row08_traceSegment_092_0283_0020, g32p_row08_traceSegment_092_0303_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0243_0081 : g32p_coeffSegment g32p_row08_traceSegment_092 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 243 40 41, g32p_row08_traceSegment_092_0243_0040, g32p_row08_traceSegment_092_0283_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0162_0162 : g32p_coeffSegment g32p_row08_traceSegment_092 162 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 162 81 81, g32p_row08_traceSegment_092_0162_0081, g32p_row08_traceSegment_092_0243_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0000_0324 : g32p_coeffSegment g32p_row08_traceSegment_092 0 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 0 162 162, g32p_row08_traceSegment_092_0000_0162, g32p_row08_traceSegment_092_0162_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0324_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 324 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0334_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 334 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0324_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 324 10 10, g32p_row08_traceSegment_092_0324_0010, g32p_row08_traceSegment_092_0334_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0344_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 344 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0354_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 354 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0344_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 344 10 10, g32p_row08_traceSegment_092_0344_0010, g32p_row08_traceSegment_092_0354_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0324_0040 : g32p_coeffSegment g32p_row08_traceSegment_092 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 324 20 20, g32p_row08_traceSegment_092_0324_0020, g32p_row08_traceSegment_092_0344_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0364_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 364 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0374_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 374 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0364_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 364 10 10, g32p_row08_traceSegment_092_0364_0010, g32p_row08_traceSegment_092_0374_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0384_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 384 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0394_0011 : g32p_coeffSegment g32p_row08_traceSegment_092 394 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0384_0021 : g32p_coeffSegment g32p_row08_traceSegment_092 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 384 10 11, g32p_row08_traceSegment_092_0384_0010, g32p_row08_traceSegment_092_0394_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0364_0041 : g32p_coeffSegment g32p_row08_traceSegment_092 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 364 20 21, g32p_row08_traceSegment_092_0364_0020, g32p_row08_traceSegment_092_0384_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0324_0081 : g32p_coeffSegment g32p_row08_traceSegment_092 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 324 40 41, g32p_row08_traceSegment_092_0324_0040, g32p_row08_traceSegment_092_0364_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0405_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 405 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0415_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 415 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0405_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 405 10 10, g32p_row08_traceSegment_092_0405_0010, g32p_row08_traceSegment_092_0415_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0425_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 425 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0435_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 435 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0425_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 425 10 10, g32p_row08_traceSegment_092_0425_0010, g32p_row08_traceSegment_092_0435_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0405_0040 : g32p_coeffSegment g32p_row08_traceSegment_092 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 405 20 20, g32p_row08_traceSegment_092_0405_0020, g32p_row08_traceSegment_092_0425_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0445_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 445 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0455_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 455 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0445_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 445 10 10, g32p_row08_traceSegment_092_0445_0010, g32p_row08_traceSegment_092_0455_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0465_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 465 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0475_0011 : g32p_coeffSegment g32p_row08_traceSegment_092 475 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0465_0021 : g32p_coeffSegment g32p_row08_traceSegment_092 465 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 465 10 11, g32p_row08_traceSegment_092_0465_0010, g32p_row08_traceSegment_092_0475_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0445_0041 : g32p_coeffSegment g32p_row08_traceSegment_092 445 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 445 20 21, g32p_row08_traceSegment_092_0445_0020, g32p_row08_traceSegment_092_0465_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0405_0081 : g32p_coeffSegment g32p_row08_traceSegment_092 405 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 405 40 41, g32p_row08_traceSegment_092_0405_0040, g32p_row08_traceSegment_092_0445_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0324_0162 : g32p_coeffSegment g32p_row08_traceSegment_092 324 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 324 81 81, g32p_row08_traceSegment_092_0324_0081, g32p_row08_traceSegment_092_0405_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0486_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 486 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0496_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 496 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0486_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 486 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 486 10 10, g32p_row08_traceSegment_092_0486_0010, g32p_row08_traceSegment_092_0496_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0506_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 506 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0516_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 516 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0506_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 506 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 506 10 10, g32p_row08_traceSegment_092_0506_0010, g32p_row08_traceSegment_092_0516_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0486_0040 : g32p_coeffSegment g32p_row08_traceSegment_092 486 40 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 486 20 20, g32p_row08_traceSegment_092_0486_0020, g32p_row08_traceSegment_092_0506_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0526_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 526 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0536_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 536 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0526_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 526 10 10, g32p_row08_traceSegment_092_0526_0010, g32p_row08_traceSegment_092_0536_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0546_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 546 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0556_0011 : g32p_coeffSegment g32p_row08_traceSegment_092 556 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0546_0021 : g32p_coeffSegment g32p_row08_traceSegment_092 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 546 10 11, g32p_row08_traceSegment_092_0546_0010, g32p_row08_traceSegment_092_0556_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0526_0041 : g32p_coeffSegment g32p_row08_traceSegment_092 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 526 20 21, g32p_row08_traceSegment_092_0526_0020, g32p_row08_traceSegment_092_0546_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0486_0081 : g32p_coeffSegment g32p_row08_traceSegment_092 486 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 486 40 41, g32p_row08_traceSegment_092_0486_0040, g32p_row08_traceSegment_092_0526_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0567_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 567 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0577_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 577 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0567_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 567 10 10, g32p_row08_traceSegment_092_0567_0010, g32p_row08_traceSegment_092_0577_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0587_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 587 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0597_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 597 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0587_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 587 10 10, g32p_row08_traceSegment_092_0587_0010, g32p_row08_traceSegment_092_0597_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0567_0040 : g32p_coeffSegment g32p_row08_traceSegment_092 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 567 20 20, g32p_row08_traceSegment_092_0567_0020, g32p_row08_traceSegment_092_0587_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0607_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 607 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0617_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 617 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0607_0020 : g32p_coeffSegment g32p_row08_traceSegment_092 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 607 10 10, g32p_row08_traceSegment_092_0607_0010, g32p_row08_traceSegment_092_0617_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0627_0010 : g32p_coeffSegment g32p_row08_traceSegment_092 627 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0637_0011 : g32p_coeffSegment g32p_row08_traceSegment_092 637 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_092_0627_0021 : g32p_coeffSegment g32p_row08_traceSegment_092 627 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 627 10 11, g32p_row08_traceSegment_092_0627_0010, g32p_row08_traceSegment_092_0637_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0607_0041 : g32p_coeffSegment g32p_row08_traceSegment_092 607 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 607 20 21, g32p_row08_traceSegment_092_0607_0020, g32p_row08_traceSegment_092_0627_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0567_0081 : g32p_coeffSegment g32p_row08_traceSegment_092 567 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 567 40 41, g32p_row08_traceSegment_092_0567_0040, g32p_row08_traceSegment_092_0607_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0486_0162 : g32p_coeffSegment g32p_row08_traceSegment_092 486 162 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 486 81 81, g32p_row08_traceSegment_092_0486_0081, g32p_row08_traceSegment_092_0567_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0324_0324 : g32p_coeffSegment g32p_row08_traceSegment_092 324 324 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 324 162 162, g32p_row08_traceSegment_092_0324_0162, g32p_row08_traceSegment_092_0486_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_092_0000_0648 : g32p_coeffSegment g32p_row08_traceSegment_092 0 648 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_092 0 324 324, g32p_row08_traceSegment_092_0000_0324, g32p_row08_traceSegment_092_0324_0324]
  decide +kernel

theorem g32p_row08_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 92 = [0, 0, 0, 0, 6] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row08_traceSegment_092_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row08_traceSegment_093 (k : ℕ) : List ℤ :=
  if g32p_row08_supplierClassifier (Fin.ofNat 648 k) = 93 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row08_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row08_traceSegment_093_0000_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 0 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0010_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 10 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0000_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 0 10 10, g32p_row08_traceSegment_093_0000_0010, g32p_row08_traceSegment_093_0010_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0020_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 20 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0030_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 30 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0020_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 20 10 10, g32p_row08_traceSegment_093_0020_0010, g32p_row08_traceSegment_093_0030_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0000_0040 : g32p_coeffSegment g32p_row08_traceSegment_093 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 0 20 20, g32p_row08_traceSegment_093_0000_0020, g32p_row08_traceSegment_093_0020_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0040_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 40 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0050_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 50 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0040_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 40 10 10, g32p_row08_traceSegment_093_0040_0010, g32p_row08_traceSegment_093_0050_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0060_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 60 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0070_0011 : g32p_coeffSegment g32p_row08_traceSegment_093 70 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0060_0021 : g32p_coeffSegment g32p_row08_traceSegment_093 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 60 10 11, g32p_row08_traceSegment_093_0060_0010, g32p_row08_traceSegment_093_0070_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0040_0041 : g32p_coeffSegment g32p_row08_traceSegment_093 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 40 20 21, g32p_row08_traceSegment_093_0040_0020, g32p_row08_traceSegment_093_0060_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0000_0081 : g32p_coeffSegment g32p_row08_traceSegment_093 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 0 40 41, g32p_row08_traceSegment_093_0000_0040, g32p_row08_traceSegment_093_0040_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0081_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 81 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0091_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 91 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0081_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 81 10 10, g32p_row08_traceSegment_093_0081_0010, g32p_row08_traceSegment_093_0091_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0101_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 101 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0111_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 111 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0101_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 101 10 10, g32p_row08_traceSegment_093_0101_0010, g32p_row08_traceSegment_093_0111_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0081_0040 : g32p_coeffSegment g32p_row08_traceSegment_093 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 81 20 20, g32p_row08_traceSegment_093_0081_0020, g32p_row08_traceSegment_093_0101_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0121_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 121 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0131_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 131 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0121_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 121 10 10, g32p_row08_traceSegment_093_0121_0010, g32p_row08_traceSegment_093_0131_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0141_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 141 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0151_0011 : g32p_coeffSegment g32p_row08_traceSegment_093 151 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0141_0021 : g32p_coeffSegment g32p_row08_traceSegment_093 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 141 10 11, g32p_row08_traceSegment_093_0141_0010, g32p_row08_traceSegment_093_0151_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0121_0041 : g32p_coeffSegment g32p_row08_traceSegment_093 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 121 20 21, g32p_row08_traceSegment_093_0121_0020, g32p_row08_traceSegment_093_0141_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0081_0081 : g32p_coeffSegment g32p_row08_traceSegment_093 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 81 40 41, g32p_row08_traceSegment_093_0081_0040, g32p_row08_traceSegment_093_0121_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0000_0162 : g32p_coeffSegment g32p_row08_traceSegment_093 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 0 81 81, g32p_row08_traceSegment_093_0000_0081, g32p_row08_traceSegment_093_0081_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0162_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 162 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0172_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 172 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0162_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 162 10 10, g32p_row08_traceSegment_093_0162_0010, g32p_row08_traceSegment_093_0172_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0182_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 182 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0192_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 192 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0182_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 182 10 10, g32p_row08_traceSegment_093_0182_0010, g32p_row08_traceSegment_093_0192_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0162_0040 : g32p_coeffSegment g32p_row08_traceSegment_093 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 162 20 20, g32p_row08_traceSegment_093_0162_0020, g32p_row08_traceSegment_093_0182_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0202_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 202 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0212_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 212 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0202_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 202 10 10, g32p_row08_traceSegment_093_0202_0010, g32p_row08_traceSegment_093_0212_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0222_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 222 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0232_0011 : g32p_coeffSegment g32p_row08_traceSegment_093 232 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0222_0021 : g32p_coeffSegment g32p_row08_traceSegment_093 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 222 10 11, g32p_row08_traceSegment_093_0222_0010, g32p_row08_traceSegment_093_0232_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0202_0041 : g32p_coeffSegment g32p_row08_traceSegment_093 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 202 20 21, g32p_row08_traceSegment_093_0202_0020, g32p_row08_traceSegment_093_0222_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0162_0081 : g32p_coeffSegment g32p_row08_traceSegment_093 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 162 40 41, g32p_row08_traceSegment_093_0162_0040, g32p_row08_traceSegment_093_0202_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0243_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 243 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0253_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 253 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0243_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 243 10 10, g32p_row08_traceSegment_093_0243_0010, g32p_row08_traceSegment_093_0253_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0263_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 263 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0273_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 273 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0263_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 263 10 10, g32p_row08_traceSegment_093_0263_0010, g32p_row08_traceSegment_093_0273_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0243_0040 : g32p_coeffSegment g32p_row08_traceSegment_093 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 243 20 20, g32p_row08_traceSegment_093_0243_0020, g32p_row08_traceSegment_093_0263_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0283_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 283 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0293_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 293 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0283_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 283 10 10, g32p_row08_traceSegment_093_0283_0010, g32p_row08_traceSegment_093_0293_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0303_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 303 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0313_0011 : g32p_coeffSegment g32p_row08_traceSegment_093 313 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0303_0021 : g32p_coeffSegment g32p_row08_traceSegment_093 303 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 303 10 11, g32p_row08_traceSegment_093_0303_0010, g32p_row08_traceSegment_093_0313_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0283_0041 : g32p_coeffSegment g32p_row08_traceSegment_093 283 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 283 20 21, g32p_row08_traceSegment_093_0283_0020, g32p_row08_traceSegment_093_0303_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0243_0081 : g32p_coeffSegment g32p_row08_traceSegment_093 243 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 243 40 41, g32p_row08_traceSegment_093_0243_0040, g32p_row08_traceSegment_093_0283_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0162_0162 : g32p_coeffSegment g32p_row08_traceSegment_093 162 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 162 81 81, g32p_row08_traceSegment_093_0162_0081, g32p_row08_traceSegment_093_0243_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0000_0324 : g32p_coeffSegment g32p_row08_traceSegment_093 0 324 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 0 162 162, g32p_row08_traceSegment_093_0000_0162, g32p_row08_traceSegment_093_0162_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0324_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 324 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0334_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 334 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0324_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 324 10 10, g32p_row08_traceSegment_093_0324_0010, g32p_row08_traceSegment_093_0334_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0344_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 344 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0354_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 354 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0344_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 344 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 344 10 10, g32p_row08_traceSegment_093_0344_0010, g32p_row08_traceSegment_093_0354_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0324_0040 : g32p_coeffSegment g32p_row08_traceSegment_093 324 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 324 20 20, g32p_row08_traceSegment_093_0324_0020, g32p_row08_traceSegment_093_0344_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0364_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 364 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0374_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 374 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0364_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 364 10 10, g32p_row08_traceSegment_093_0364_0010, g32p_row08_traceSegment_093_0374_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0384_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 384 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0394_0011 : g32p_coeffSegment g32p_row08_traceSegment_093 394 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0384_0021 : g32p_coeffSegment g32p_row08_traceSegment_093 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 384 10 11, g32p_row08_traceSegment_093_0384_0010, g32p_row08_traceSegment_093_0394_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0364_0041 : g32p_coeffSegment g32p_row08_traceSegment_093 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 364 20 21, g32p_row08_traceSegment_093_0364_0020, g32p_row08_traceSegment_093_0384_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0324_0081 : g32p_coeffSegment g32p_row08_traceSegment_093 324 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 324 40 41, g32p_row08_traceSegment_093_0324_0040, g32p_row08_traceSegment_093_0364_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0405_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 405 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0415_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 415 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0405_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 405 10 10, g32p_row08_traceSegment_093_0405_0010, g32p_row08_traceSegment_093_0415_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0425_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 425 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0435_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 435 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0425_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 425 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 425 10 10, g32p_row08_traceSegment_093_0425_0010, g32p_row08_traceSegment_093_0435_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0405_0040 : g32p_coeffSegment g32p_row08_traceSegment_093 405 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 405 20 20, g32p_row08_traceSegment_093_0405_0020, g32p_row08_traceSegment_093_0425_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0445_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 445 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0455_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 455 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0445_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 445 10 10, g32p_row08_traceSegment_093_0445_0010, g32p_row08_traceSegment_093_0455_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0465_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 465 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0475_0011 : g32p_coeffSegment g32p_row08_traceSegment_093 475 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0465_0021 : g32p_coeffSegment g32p_row08_traceSegment_093 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 465 10 11, g32p_row08_traceSegment_093_0465_0010, g32p_row08_traceSegment_093_0475_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0445_0041 : g32p_coeffSegment g32p_row08_traceSegment_093 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 445 20 21, g32p_row08_traceSegment_093_0445_0020, g32p_row08_traceSegment_093_0465_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0405_0081 : g32p_coeffSegment g32p_row08_traceSegment_093 405 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 405 40 41, g32p_row08_traceSegment_093_0405_0040, g32p_row08_traceSegment_093_0445_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0324_0162 : g32p_coeffSegment g32p_row08_traceSegment_093 324 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 324 81 81, g32p_row08_traceSegment_093_0324_0081, g32p_row08_traceSegment_093_0405_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0486_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 486 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0496_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 496 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0486_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 486 10 10, g32p_row08_traceSegment_093_0486_0010, g32p_row08_traceSegment_093_0496_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0506_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 506 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0516_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 516 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0506_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 506 10 10, g32p_row08_traceSegment_093_0506_0010, g32p_row08_traceSegment_093_0516_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0486_0040 : g32p_coeffSegment g32p_row08_traceSegment_093 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 486 20 20, g32p_row08_traceSegment_093_0486_0020, g32p_row08_traceSegment_093_0506_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0526_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 526 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0536_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 536 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0526_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 526 10 10, g32p_row08_traceSegment_093_0526_0010, g32p_row08_traceSegment_093_0536_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0546_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 546 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0556_0011 : g32p_coeffSegment g32p_row08_traceSegment_093 556 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0546_0021 : g32p_coeffSegment g32p_row08_traceSegment_093 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 546 10 11, g32p_row08_traceSegment_093_0546_0010, g32p_row08_traceSegment_093_0556_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0526_0041 : g32p_coeffSegment g32p_row08_traceSegment_093 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 526 20 21, g32p_row08_traceSegment_093_0526_0020, g32p_row08_traceSegment_093_0546_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0486_0081 : g32p_coeffSegment g32p_row08_traceSegment_093 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 486 40 41, g32p_row08_traceSegment_093_0486_0040, g32p_row08_traceSegment_093_0526_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0567_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 567 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0577_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 577 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0567_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 567 10 10, g32p_row08_traceSegment_093_0567_0010, g32p_row08_traceSegment_093_0577_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0587_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 587 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0597_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 597 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0587_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 587 10 10, g32p_row08_traceSegment_093_0587_0010, g32p_row08_traceSegment_093_0597_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0567_0040 : g32p_coeffSegment g32p_row08_traceSegment_093 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 567 20 20, g32p_row08_traceSegment_093_0567_0020, g32p_row08_traceSegment_093_0587_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0607_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 607 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0617_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 617 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0607_0020 : g32p_coeffSegment g32p_row08_traceSegment_093 607 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 607 10 10, g32p_row08_traceSegment_093_0607_0010, g32p_row08_traceSegment_093_0617_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0627_0010 : g32p_coeffSegment g32p_row08_traceSegment_093 627 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0637_0011 : g32p_coeffSegment g32p_row08_traceSegment_093 637 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_093_0627_0021 : g32p_coeffSegment g32p_row08_traceSegment_093 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 627 10 11, g32p_row08_traceSegment_093_0627_0010, g32p_row08_traceSegment_093_0637_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0607_0041 : g32p_coeffSegment g32p_row08_traceSegment_093 607 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 607 20 21, g32p_row08_traceSegment_093_0607_0020, g32p_row08_traceSegment_093_0627_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0567_0081 : g32p_coeffSegment g32p_row08_traceSegment_093 567 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 567 40 41, g32p_row08_traceSegment_093_0567_0040, g32p_row08_traceSegment_093_0607_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0486_0162 : g32p_coeffSegment g32p_row08_traceSegment_093 486 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 486 81 81, g32p_row08_traceSegment_093_0486_0081, g32p_row08_traceSegment_093_0567_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0324_0324 : g32p_coeffSegment g32p_row08_traceSegment_093 324 324 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 324 162 162, g32p_row08_traceSegment_093_0324_0162, g32p_row08_traceSegment_093_0486_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_093_0000_0648 : g32p_coeffSegment g32p_row08_traceSegment_093 0 648 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_093 0 324 324, g32p_row08_traceSegment_093_0000_0324, g32p_row08_traceSegment_093_0324_0324]
  decide +kernel

theorem g32p_row08_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 93 = [0, 0, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row08_traceSegment_093_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row08_traceSegment_095 (k : ℕ) : List ℤ :=
  if g32p_row08_supplierClassifier (Fin.ofNat 648 k) = 95 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row08_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row08_traceSegment_095_0000_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 0 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0010_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 10 10 = [1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0000_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 0 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 0 10 10, g32p_row08_traceSegment_095_0000_0010, g32p_row08_traceSegment_095_0010_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0020_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 20 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0030_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 30 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0020_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 20 10 10, g32p_row08_traceSegment_095_0020_0010, g32p_row08_traceSegment_095_0030_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0000_0040 : g32p_coeffSegment g32p_row08_traceSegment_095 0 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 0 20 20, g32p_row08_traceSegment_095_0000_0020, g32p_row08_traceSegment_095_0020_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0040_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 40 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0050_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 50 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0040_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 40 10 10, g32p_row08_traceSegment_095_0040_0010, g32p_row08_traceSegment_095_0050_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0060_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 60 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0070_0011 : g32p_coeffSegment g32p_row08_traceSegment_095 70 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0060_0021 : g32p_coeffSegment g32p_row08_traceSegment_095 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 60 10 11, g32p_row08_traceSegment_095_0060_0010, g32p_row08_traceSegment_095_0070_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0040_0041 : g32p_coeffSegment g32p_row08_traceSegment_095 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 40 20 21, g32p_row08_traceSegment_095_0040_0020, g32p_row08_traceSegment_095_0060_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0000_0081 : g32p_coeffSegment g32p_row08_traceSegment_095 0 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 0 40 41, g32p_row08_traceSegment_095_0000_0040, g32p_row08_traceSegment_095_0040_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0081_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 81 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0091_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 91 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0081_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 81 10 10, g32p_row08_traceSegment_095_0081_0010, g32p_row08_traceSegment_095_0091_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0101_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 101 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0111_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 111 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0101_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 101 10 10, g32p_row08_traceSegment_095_0101_0010, g32p_row08_traceSegment_095_0111_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0081_0040 : g32p_coeffSegment g32p_row08_traceSegment_095 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 81 20 20, g32p_row08_traceSegment_095_0081_0020, g32p_row08_traceSegment_095_0101_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0121_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 121 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0131_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 131 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0121_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 121 10 10, g32p_row08_traceSegment_095_0121_0010, g32p_row08_traceSegment_095_0131_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0141_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 141 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0151_0011 : g32p_coeffSegment g32p_row08_traceSegment_095 151 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0141_0021 : g32p_coeffSegment g32p_row08_traceSegment_095 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 141 10 11, g32p_row08_traceSegment_095_0141_0010, g32p_row08_traceSegment_095_0151_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0121_0041 : g32p_coeffSegment g32p_row08_traceSegment_095 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 121 20 21, g32p_row08_traceSegment_095_0121_0020, g32p_row08_traceSegment_095_0141_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0081_0081 : g32p_coeffSegment g32p_row08_traceSegment_095 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 81 40 41, g32p_row08_traceSegment_095_0081_0040, g32p_row08_traceSegment_095_0121_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0000_0162 : g32p_coeffSegment g32p_row08_traceSegment_095 0 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 0 81 81, g32p_row08_traceSegment_095_0000_0081, g32p_row08_traceSegment_095_0081_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0162_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 162 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0172_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 172 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0162_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 162 10 10, g32p_row08_traceSegment_095_0162_0010, g32p_row08_traceSegment_095_0172_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0182_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 182 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0192_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 192 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0182_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 182 10 10, g32p_row08_traceSegment_095_0182_0010, g32p_row08_traceSegment_095_0192_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0162_0040 : g32p_coeffSegment g32p_row08_traceSegment_095 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 162 20 20, g32p_row08_traceSegment_095_0162_0020, g32p_row08_traceSegment_095_0182_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0202_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 202 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0212_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 212 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0202_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 202 10 10, g32p_row08_traceSegment_095_0202_0010, g32p_row08_traceSegment_095_0212_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0222_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 222 10 = [1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0232_0011 : g32p_coeffSegment g32p_row08_traceSegment_095 232 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0222_0021 : g32p_coeffSegment g32p_row08_traceSegment_095 222 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 222 10 11, g32p_row08_traceSegment_095_0222_0010, g32p_row08_traceSegment_095_0232_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0202_0041 : g32p_coeffSegment g32p_row08_traceSegment_095 202 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 202 20 21, g32p_row08_traceSegment_095_0202_0020, g32p_row08_traceSegment_095_0222_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0162_0081 : g32p_coeffSegment g32p_row08_traceSegment_095 162 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 162 40 41, g32p_row08_traceSegment_095_0162_0040, g32p_row08_traceSegment_095_0202_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0243_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 243 10 = [1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0253_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 253 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0243_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 243 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 243 10 10, g32p_row08_traceSegment_095_0243_0010, g32p_row08_traceSegment_095_0253_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0263_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 263 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0273_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 273 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0263_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 263 10 10, g32p_row08_traceSegment_095_0263_0010, g32p_row08_traceSegment_095_0273_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0243_0040 : g32p_coeffSegment g32p_row08_traceSegment_095 243 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 243 20 20, g32p_row08_traceSegment_095_0243_0020, g32p_row08_traceSegment_095_0263_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0283_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 283 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0293_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 293 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0283_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 283 10 10, g32p_row08_traceSegment_095_0283_0010, g32p_row08_traceSegment_095_0293_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0303_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 303 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0313_0011 : g32p_coeffSegment g32p_row08_traceSegment_095 313 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0303_0021 : g32p_coeffSegment g32p_row08_traceSegment_095 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 303 10 11, g32p_row08_traceSegment_095_0303_0010, g32p_row08_traceSegment_095_0313_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0283_0041 : g32p_coeffSegment g32p_row08_traceSegment_095 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 283 20 21, g32p_row08_traceSegment_095_0283_0020, g32p_row08_traceSegment_095_0303_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0243_0081 : g32p_coeffSegment g32p_row08_traceSegment_095 243 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 243 40 41, g32p_row08_traceSegment_095_0243_0040, g32p_row08_traceSegment_095_0283_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0162_0162 : g32p_coeffSegment g32p_row08_traceSegment_095 162 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 162 81 81, g32p_row08_traceSegment_095_0162_0081, g32p_row08_traceSegment_095_0243_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0000_0324 : g32p_coeffSegment g32p_row08_traceSegment_095 0 324 = [3] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 0 162 162, g32p_row08_traceSegment_095_0000_0162, g32p_row08_traceSegment_095_0162_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0324_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 324 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0334_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 334 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0324_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 324 10 10, g32p_row08_traceSegment_095_0324_0010, g32p_row08_traceSegment_095_0334_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0344_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 344 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0354_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 354 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0344_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 344 10 10, g32p_row08_traceSegment_095_0344_0010, g32p_row08_traceSegment_095_0354_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0324_0040 : g32p_coeffSegment g32p_row08_traceSegment_095 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 324 20 20, g32p_row08_traceSegment_095_0324_0020, g32p_row08_traceSegment_095_0344_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0364_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 364 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0374_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 374 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0364_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 364 10 10, g32p_row08_traceSegment_095_0364_0010, g32p_row08_traceSegment_095_0374_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0384_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 384 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0394_0011 : g32p_coeffSegment g32p_row08_traceSegment_095 394 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0384_0021 : g32p_coeffSegment g32p_row08_traceSegment_095 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 384 10 11, g32p_row08_traceSegment_095_0384_0010, g32p_row08_traceSegment_095_0394_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0364_0041 : g32p_coeffSegment g32p_row08_traceSegment_095 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 364 20 21, g32p_row08_traceSegment_095_0364_0020, g32p_row08_traceSegment_095_0384_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0324_0081 : g32p_coeffSegment g32p_row08_traceSegment_095 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 324 40 41, g32p_row08_traceSegment_095_0324_0040, g32p_row08_traceSegment_095_0364_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0405_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 405 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0415_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 415 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0405_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 405 10 10, g32p_row08_traceSegment_095_0405_0010, g32p_row08_traceSegment_095_0415_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0425_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 425 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0435_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 435 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0425_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 425 10 10, g32p_row08_traceSegment_095_0425_0010, g32p_row08_traceSegment_095_0435_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0405_0040 : g32p_coeffSegment g32p_row08_traceSegment_095 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 405 20 20, g32p_row08_traceSegment_095_0405_0020, g32p_row08_traceSegment_095_0425_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0445_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 445 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0455_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 455 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0445_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 445 10 10, g32p_row08_traceSegment_095_0445_0010, g32p_row08_traceSegment_095_0455_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0465_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 465 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0475_0011 : g32p_coeffSegment g32p_row08_traceSegment_095 475 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0465_0021 : g32p_coeffSegment g32p_row08_traceSegment_095 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 465 10 11, g32p_row08_traceSegment_095_0465_0010, g32p_row08_traceSegment_095_0475_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0445_0041 : g32p_coeffSegment g32p_row08_traceSegment_095 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 445 20 21, g32p_row08_traceSegment_095_0445_0020, g32p_row08_traceSegment_095_0465_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0405_0081 : g32p_coeffSegment g32p_row08_traceSegment_095 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 405 40 41, g32p_row08_traceSegment_095_0405_0040, g32p_row08_traceSegment_095_0445_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0324_0162 : g32p_coeffSegment g32p_row08_traceSegment_095 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 324 81 81, g32p_row08_traceSegment_095_0324_0081, g32p_row08_traceSegment_095_0405_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0486_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 486 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0496_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 496 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0486_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 486 10 10, g32p_row08_traceSegment_095_0486_0010, g32p_row08_traceSegment_095_0496_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0506_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 506 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0516_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 516 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0506_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 506 10 10, g32p_row08_traceSegment_095_0506_0010, g32p_row08_traceSegment_095_0516_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0486_0040 : g32p_coeffSegment g32p_row08_traceSegment_095 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 486 20 20, g32p_row08_traceSegment_095_0486_0020, g32p_row08_traceSegment_095_0506_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0526_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 526 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0536_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 536 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0526_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 526 10 10, g32p_row08_traceSegment_095_0526_0010, g32p_row08_traceSegment_095_0536_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0546_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 546 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0556_0011 : g32p_coeffSegment g32p_row08_traceSegment_095 556 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0546_0021 : g32p_coeffSegment g32p_row08_traceSegment_095 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 546 10 11, g32p_row08_traceSegment_095_0546_0010, g32p_row08_traceSegment_095_0556_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0526_0041 : g32p_coeffSegment g32p_row08_traceSegment_095 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 526 20 21, g32p_row08_traceSegment_095_0526_0020, g32p_row08_traceSegment_095_0546_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0486_0081 : g32p_coeffSegment g32p_row08_traceSegment_095 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 486 40 41, g32p_row08_traceSegment_095_0486_0040, g32p_row08_traceSegment_095_0526_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0567_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 567 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0577_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 577 10 = [1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0567_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 567 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 567 10 10, g32p_row08_traceSegment_095_0567_0010, g32p_row08_traceSegment_095_0577_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0587_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 587 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0597_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 597 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0587_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 587 10 10, g32p_row08_traceSegment_095_0587_0010, g32p_row08_traceSegment_095_0597_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0567_0040 : g32p_coeffSegment g32p_row08_traceSegment_095 567 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 567 20 20, g32p_row08_traceSegment_095_0567_0020, g32p_row08_traceSegment_095_0587_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0607_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 607 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0617_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 617 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0607_0020 : g32p_coeffSegment g32p_row08_traceSegment_095 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 607 10 10, g32p_row08_traceSegment_095_0607_0010, g32p_row08_traceSegment_095_0617_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0627_0010 : g32p_coeffSegment g32p_row08_traceSegment_095 627 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0637_0011 : g32p_coeffSegment g32p_row08_traceSegment_095 637 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_095_0627_0021 : g32p_coeffSegment g32p_row08_traceSegment_095 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 627 10 11, g32p_row08_traceSegment_095_0627_0010, g32p_row08_traceSegment_095_0637_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0607_0041 : g32p_coeffSegment g32p_row08_traceSegment_095 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 607 20 21, g32p_row08_traceSegment_095_0607_0020, g32p_row08_traceSegment_095_0627_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0567_0081 : g32p_coeffSegment g32p_row08_traceSegment_095 567 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 567 40 41, g32p_row08_traceSegment_095_0567_0040, g32p_row08_traceSegment_095_0607_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0486_0162 : g32p_coeffSegment g32p_row08_traceSegment_095 486 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 486 81 81, g32p_row08_traceSegment_095_0486_0081, g32p_row08_traceSegment_095_0567_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0324_0324 : g32p_coeffSegment g32p_row08_traceSegment_095 324 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 324 162 162, g32p_row08_traceSegment_095_0324_0162, g32p_row08_traceSegment_095_0486_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_095_0000_0648 : g32p_coeffSegment g32p_row08_traceSegment_095 0 648 = [4] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_095 0 324 324, g32p_row08_traceSegment_095_0000_0324, g32p_row08_traceSegment_095_0324_0324]
  decide +kernel

theorem g32p_row08_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 95 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row08_traceSegment_095_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row08_traceSegment_096 (k : ℕ) : List ℤ :=
  if g32p_row08_supplierClassifier (Fin.ofNat 648 k) = 96 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row08_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row08_traceSegment_096_0000_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 0 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0010_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 10 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0000_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 0 10 10, g32p_row08_traceSegment_096_0000_0010, g32p_row08_traceSegment_096_0010_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0020_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 20 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0030_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 30 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0020_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 20 10 10, g32p_row08_traceSegment_096_0020_0010, g32p_row08_traceSegment_096_0030_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0000_0040 : g32p_coeffSegment g32p_row08_traceSegment_096 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 0 20 20, g32p_row08_traceSegment_096_0000_0020, g32p_row08_traceSegment_096_0020_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0040_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 40 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0050_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 50 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0040_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 40 10 10, g32p_row08_traceSegment_096_0040_0010, g32p_row08_traceSegment_096_0050_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0060_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 60 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0070_0011 : g32p_coeffSegment g32p_row08_traceSegment_096 70 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0060_0021 : g32p_coeffSegment g32p_row08_traceSegment_096 60 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 60 10 11, g32p_row08_traceSegment_096_0060_0010, g32p_row08_traceSegment_096_0070_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0040_0041 : g32p_coeffSegment g32p_row08_traceSegment_096 40 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 40 20 21, g32p_row08_traceSegment_096_0040_0020, g32p_row08_traceSegment_096_0060_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0000_0081 : g32p_coeffSegment g32p_row08_traceSegment_096 0 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 0 40 41, g32p_row08_traceSegment_096_0000_0040, g32p_row08_traceSegment_096_0040_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0081_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 81 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0091_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 91 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0081_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 81 10 10, g32p_row08_traceSegment_096_0081_0010, g32p_row08_traceSegment_096_0091_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0101_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 101 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0111_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 111 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0101_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 101 10 10, g32p_row08_traceSegment_096_0101_0010, g32p_row08_traceSegment_096_0111_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0081_0040 : g32p_coeffSegment g32p_row08_traceSegment_096 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 81 20 20, g32p_row08_traceSegment_096_0081_0020, g32p_row08_traceSegment_096_0101_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0121_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 121 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0131_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 131 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0121_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 121 10 10, g32p_row08_traceSegment_096_0121_0010, g32p_row08_traceSegment_096_0131_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0141_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 141 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0151_0011 : g32p_coeffSegment g32p_row08_traceSegment_096 151 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0141_0021 : g32p_coeffSegment g32p_row08_traceSegment_096 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 141 10 11, g32p_row08_traceSegment_096_0141_0010, g32p_row08_traceSegment_096_0151_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0121_0041 : g32p_coeffSegment g32p_row08_traceSegment_096 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 121 20 21, g32p_row08_traceSegment_096_0121_0020, g32p_row08_traceSegment_096_0141_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0081_0081 : g32p_coeffSegment g32p_row08_traceSegment_096 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 81 40 41, g32p_row08_traceSegment_096_0081_0040, g32p_row08_traceSegment_096_0121_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0000_0162 : g32p_coeffSegment g32p_row08_traceSegment_096 0 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 0 81 81, g32p_row08_traceSegment_096_0000_0081, g32p_row08_traceSegment_096_0081_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0162_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 162 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0172_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 172 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0162_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 162 10 10, g32p_row08_traceSegment_096_0162_0010, g32p_row08_traceSegment_096_0172_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0182_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 182 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0192_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 192 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0182_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 182 10 10, g32p_row08_traceSegment_096_0182_0010, g32p_row08_traceSegment_096_0192_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0162_0040 : g32p_coeffSegment g32p_row08_traceSegment_096 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 162 20 20, g32p_row08_traceSegment_096_0162_0020, g32p_row08_traceSegment_096_0182_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0202_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 202 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0212_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 212 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0202_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 202 10 10, g32p_row08_traceSegment_096_0202_0010, g32p_row08_traceSegment_096_0212_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0222_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 222 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0232_0011 : g32p_coeffSegment g32p_row08_traceSegment_096 232 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0222_0021 : g32p_coeffSegment g32p_row08_traceSegment_096 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 222 10 11, g32p_row08_traceSegment_096_0222_0010, g32p_row08_traceSegment_096_0232_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0202_0041 : g32p_coeffSegment g32p_row08_traceSegment_096 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 202 20 21, g32p_row08_traceSegment_096_0202_0020, g32p_row08_traceSegment_096_0222_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0162_0081 : g32p_coeffSegment g32p_row08_traceSegment_096 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 162 40 41, g32p_row08_traceSegment_096_0162_0040, g32p_row08_traceSegment_096_0202_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0243_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 243 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0253_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 253 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0243_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 243 10 10, g32p_row08_traceSegment_096_0243_0010, g32p_row08_traceSegment_096_0253_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0263_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 263 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0273_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 273 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0263_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 263 10 10, g32p_row08_traceSegment_096_0263_0010, g32p_row08_traceSegment_096_0273_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0243_0040 : g32p_coeffSegment g32p_row08_traceSegment_096 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 243 20 20, g32p_row08_traceSegment_096_0243_0020, g32p_row08_traceSegment_096_0263_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0283_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 283 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0293_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 293 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0283_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 283 10 10, g32p_row08_traceSegment_096_0283_0010, g32p_row08_traceSegment_096_0293_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0303_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 303 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0313_0011 : g32p_coeffSegment g32p_row08_traceSegment_096 313 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0303_0021 : g32p_coeffSegment g32p_row08_traceSegment_096 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 303 10 11, g32p_row08_traceSegment_096_0303_0010, g32p_row08_traceSegment_096_0313_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0283_0041 : g32p_coeffSegment g32p_row08_traceSegment_096 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 283 20 21, g32p_row08_traceSegment_096_0283_0020, g32p_row08_traceSegment_096_0303_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0243_0081 : g32p_coeffSegment g32p_row08_traceSegment_096 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 243 40 41, g32p_row08_traceSegment_096_0243_0040, g32p_row08_traceSegment_096_0283_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0162_0162 : g32p_coeffSegment g32p_row08_traceSegment_096 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 162 81 81, g32p_row08_traceSegment_096_0162_0081, g32p_row08_traceSegment_096_0243_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0000_0324 : g32p_coeffSegment g32p_row08_traceSegment_096 0 324 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 0 162 162, g32p_row08_traceSegment_096_0000_0162, g32p_row08_traceSegment_096_0162_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0324_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 324 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0334_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 334 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0324_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 324 10 10, g32p_row08_traceSegment_096_0324_0010, g32p_row08_traceSegment_096_0334_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0344_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 344 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0354_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 354 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0344_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 344 10 10, g32p_row08_traceSegment_096_0344_0010, g32p_row08_traceSegment_096_0354_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0324_0040 : g32p_coeffSegment g32p_row08_traceSegment_096 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 324 20 20, g32p_row08_traceSegment_096_0324_0020, g32p_row08_traceSegment_096_0344_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0364_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 364 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0374_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 374 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0364_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 364 10 10, g32p_row08_traceSegment_096_0364_0010, g32p_row08_traceSegment_096_0374_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0384_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 384 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0394_0011 : g32p_coeffSegment g32p_row08_traceSegment_096 394 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0384_0021 : g32p_coeffSegment g32p_row08_traceSegment_096 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 384 10 11, g32p_row08_traceSegment_096_0384_0010, g32p_row08_traceSegment_096_0394_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0364_0041 : g32p_coeffSegment g32p_row08_traceSegment_096 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 364 20 21, g32p_row08_traceSegment_096_0364_0020, g32p_row08_traceSegment_096_0384_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0324_0081 : g32p_coeffSegment g32p_row08_traceSegment_096 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 324 40 41, g32p_row08_traceSegment_096_0324_0040, g32p_row08_traceSegment_096_0364_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0405_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 405 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0415_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 415 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0405_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 405 10 10, g32p_row08_traceSegment_096_0405_0010, g32p_row08_traceSegment_096_0415_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0425_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 425 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0435_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 435 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0425_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 425 10 10, g32p_row08_traceSegment_096_0425_0010, g32p_row08_traceSegment_096_0435_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0405_0040 : g32p_coeffSegment g32p_row08_traceSegment_096 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 405 20 20, g32p_row08_traceSegment_096_0405_0020, g32p_row08_traceSegment_096_0425_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0445_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 445 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0455_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 455 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0445_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 445 10 10, g32p_row08_traceSegment_096_0445_0010, g32p_row08_traceSegment_096_0455_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0465_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 465 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0475_0011 : g32p_coeffSegment g32p_row08_traceSegment_096 475 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0465_0021 : g32p_coeffSegment g32p_row08_traceSegment_096 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 465 10 11, g32p_row08_traceSegment_096_0465_0010, g32p_row08_traceSegment_096_0475_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0445_0041 : g32p_coeffSegment g32p_row08_traceSegment_096 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 445 20 21, g32p_row08_traceSegment_096_0445_0020, g32p_row08_traceSegment_096_0465_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0405_0081 : g32p_coeffSegment g32p_row08_traceSegment_096 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 405 40 41, g32p_row08_traceSegment_096_0405_0040, g32p_row08_traceSegment_096_0445_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0324_0162 : g32p_coeffSegment g32p_row08_traceSegment_096 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 324 81 81, g32p_row08_traceSegment_096_0324_0081, g32p_row08_traceSegment_096_0405_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0486_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 486 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0496_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 496 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0486_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 486 10 10, g32p_row08_traceSegment_096_0486_0010, g32p_row08_traceSegment_096_0496_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0506_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 506 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0516_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 516 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0506_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 506 10 10, g32p_row08_traceSegment_096_0506_0010, g32p_row08_traceSegment_096_0516_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0486_0040 : g32p_coeffSegment g32p_row08_traceSegment_096 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 486 20 20, g32p_row08_traceSegment_096_0486_0020, g32p_row08_traceSegment_096_0506_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0526_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 526 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0536_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 536 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0526_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 526 10 10, g32p_row08_traceSegment_096_0526_0010, g32p_row08_traceSegment_096_0536_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0546_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 546 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0556_0011 : g32p_coeffSegment g32p_row08_traceSegment_096 556 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0546_0021 : g32p_coeffSegment g32p_row08_traceSegment_096 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 546 10 11, g32p_row08_traceSegment_096_0546_0010, g32p_row08_traceSegment_096_0556_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0526_0041 : g32p_coeffSegment g32p_row08_traceSegment_096 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 526 20 21, g32p_row08_traceSegment_096_0526_0020, g32p_row08_traceSegment_096_0546_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0486_0081 : g32p_coeffSegment g32p_row08_traceSegment_096 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 486 40 41, g32p_row08_traceSegment_096_0486_0040, g32p_row08_traceSegment_096_0526_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0567_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 567 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0577_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 577 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0567_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 567 10 10, g32p_row08_traceSegment_096_0567_0010, g32p_row08_traceSegment_096_0577_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0587_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 587 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0597_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 597 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0587_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 587 10 10, g32p_row08_traceSegment_096_0587_0010, g32p_row08_traceSegment_096_0597_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0567_0040 : g32p_coeffSegment g32p_row08_traceSegment_096 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 567 20 20, g32p_row08_traceSegment_096_0567_0020, g32p_row08_traceSegment_096_0587_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0607_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 607 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0617_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 617 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0607_0020 : g32p_coeffSegment g32p_row08_traceSegment_096 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 607 10 10, g32p_row08_traceSegment_096_0607_0010, g32p_row08_traceSegment_096_0617_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0627_0010 : g32p_coeffSegment g32p_row08_traceSegment_096 627 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0637_0011 : g32p_coeffSegment g32p_row08_traceSegment_096 637 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_096_0627_0021 : g32p_coeffSegment g32p_row08_traceSegment_096 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 627 10 11, g32p_row08_traceSegment_096_0627_0010, g32p_row08_traceSegment_096_0637_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0607_0041 : g32p_coeffSegment g32p_row08_traceSegment_096 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 607 20 21, g32p_row08_traceSegment_096_0607_0020, g32p_row08_traceSegment_096_0627_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0567_0081 : g32p_coeffSegment g32p_row08_traceSegment_096 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 567 40 41, g32p_row08_traceSegment_096_0567_0040, g32p_row08_traceSegment_096_0607_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0486_0162 : g32p_coeffSegment g32p_row08_traceSegment_096 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 486 81 81, g32p_row08_traceSegment_096_0486_0081, g32p_row08_traceSegment_096_0567_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0324_0324 : g32p_coeffSegment g32p_row08_traceSegment_096 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 324 162 162, g32p_row08_traceSegment_096_0324_0162, g32p_row08_traceSegment_096_0486_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_096_0000_0648 : g32p_coeffSegment g32p_row08_traceSegment_096 0 648 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_096 0 324 324, g32p_row08_traceSegment_096_0000_0324, g32p_row08_traceSegment_096_0324_0324]
  decide +kernel

theorem g32p_row08_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 96 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row08_traceSegment_096_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row08_traceSegment_097 (k : ℕ) : List ℤ :=
  if g32p_row08_supplierClassifier (Fin.ofNat 648 k) = 97 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row08_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row08_traceSegment_097_0000_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 0 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0010_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 10 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0000_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 0 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 0 10 10, g32p_row08_traceSegment_097_0000_0010, g32p_row08_traceSegment_097_0010_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0020_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 20 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0030_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 30 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0020_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 20 10 10, g32p_row08_traceSegment_097_0020_0010, g32p_row08_traceSegment_097_0030_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0000_0040 : g32p_coeffSegment g32p_row08_traceSegment_097 0 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 0 20 20, g32p_row08_traceSegment_097_0000_0020, g32p_row08_traceSegment_097_0020_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0040_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 40 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0050_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 50 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0040_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 40 10 10, g32p_row08_traceSegment_097_0040_0010, g32p_row08_traceSegment_097_0050_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0060_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 60 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0070_0011 : g32p_coeffSegment g32p_row08_traceSegment_097 70 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0060_0021 : g32p_coeffSegment g32p_row08_traceSegment_097 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 60 10 11, g32p_row08_traceSegment_097_0060_0010, g32p_row08_traceSegment_097_0070_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0040_0041 : g32p_coeffSegment g32p_row08_traceSegment_097 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 40 20 21, g32p_row08_traceSegment_097_0040_0020, g32p_row08_traceSegment_097_0060_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0000_0081 : g32p_coeffSegment g32p_row08_traceSegment_097 0 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 0 40 41, g32p_row08_traceSegment_097_0000_0040, g32p_row08_traceSegment_097_0040_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0081_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 81 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0091_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 91 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0081_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 81 10 10, g32p_row08_traceSegment_097_0081_0010, g32p_row08_traceSegment_097_0091_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0101_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 101 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0111_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 111 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0101_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 101 10 10, g32p_row08_traceSegment_097_0101_0010, g32p_row08_traceSegment_097_0111_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0081_0040 : g32p_coeffSegment g32p_row08_traceSegment_097 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 81 20 20, g32p_row08_traceSegment_097_0081_0020, g32p_row08_traceSegment_097_0101_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0121_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 121 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0131_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 131 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0121_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 121 10 10, g32p_row08_traceSegment_097_0121_0010, g32p_row08_traceSegment_097_0131_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0141_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 141 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0151_0011 : g32p_coeffSegment g32p_row08_traceSegment_097 151 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0141_0021 : g32p_coeffSegment g32p_row08_traceSegment_097 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 141 10 11, g32p_row08_traceSegment_097_0141_0010, g32p_row08_traceSegment_097_0151_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0121_0041 : g32p_coeffSegment g32p_row08_traceSegment_097 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 121 20 21, g32p_row08_traceSegment_097_0121_0020, g32p_row08_traceSegment_097_0141_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0081_0081 : g32p_coeffSegment g32p_row08_traceSegment_097 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 81 40 41, g32p_row08_traceSegment_097_0081_0040, g32p_row08_traceSegment_097_0121_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0000_0162 : g32p_coeffSegment g32p_row08_traceSegment_097 0 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 0 81 81, g32p_row08_traceSegment_097_0000_0081, g32p_row08_traceSegment_097_0081_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0162_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 162 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0172_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 172 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0162_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 162 10 10, g32p_row08_traceSegment_097_0162_0010, g32p_row08_traceSegment_097_0172_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0182_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 182 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0192_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 192 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0182_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 182 10 10, g32p_row08_traceSegment_097_0182_0010, g32p_row08_traceSegment_097_0192_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0162_0040 : g32p_coeffSegment g32p_row08_traceSegment_097 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 162 20 20, g32p_row08_traceSegment_097_0162_0020, g32p_row08_traceSegment_097_0182_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0202_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 202 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0212_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 212 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0202_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 202 10 10, g32p_row08_traceSegment_097_0202_0010, g32p_row08_traceSegment_097_0212_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0222_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 222 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0232_0011 : g32p_coeffSegment g32p_row08_traceSegment_097 232 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0222_0021 : g32p_coeffSegment g32p_row08_traceSegment_097 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 222 10 11, g32p_row08_traceSegment_097_0222_0010, g32p_row08_traceSegment_097_0232_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0202_0041 : g32p_coeffSegment g32p_row08_traceSegment_097 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 202 20 21, g32p_row08_traceSegment_097_0202_0020, g32p_row08_traceSegment_097_0222_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0162_0081 : g32p_coeffSegment g32p_row08_traceSegment_097 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 162 40 41, g32p_row08_traceSegment_097_0162_0040, g32p_row08_traceSegment_097_0202_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0243_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 243 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0253_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 253 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0243_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 243 10 10, g32p_row08_traceSegment_097_0243_0010, g32p_row08_traceSegment_097_0253_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0263_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 263 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0273_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 273 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0263_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 263 10 10, g32p_row08_traceSegment_097_0263_0010, g32p_row08_traceSegment_097_0273_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0243_0040 : g32p_coeffSegment g32p_row08_traceSegment_097 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 243 20 20, g32p_row08_traceSegment_097_0243_0020, g32p_row08_traceSegment_097_0263_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0283_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 283 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0293_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 293 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0283_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 283 10 10, g32p_row08_traceSegment_097_0283_0010, g32p_row08_traceSegment_097_0293_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0303_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 303 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0313_0011 : g32p_coeffSegment g32p_row08_traceSegment_097 313 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0303_0021 : g32p_coeffSegment g32p_row08_traceSegment_097 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 303 10 11, g32p_row08_traceSegment_097_0303_0010, g32p_row08_traceSegment_097_0313_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0283_0041 : g32p_coeffSegment g32p_row08_traceSegment_097 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 283 20 21, g32p_row08_traceSegment_097_0283_0020, g32p_row08_traceSegment_097_0303_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0243_0081 : g32p_coeffSegment g32p_row08_traceSegment_097 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 243 40 41, g32p_row08_traceSegment_097_0243_0040, g32p_row08_traceSegment_097_0283_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0162_0162 : g32p_coeffSegment g32p_row08_traceSegment_097 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 162 81 81, g32p_row08_traceSegment_097_0162_0081, g32p_row08_traceSegment_097_0243_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0000_0324 : g32p_coeffSegment g32p_row08_traceSegment_097 0 324 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 0 162 162, g32p_row08_traceSegment_097_0000_0162, g32p_row08_traceSegment_097_0162_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0324_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 324 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0334_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 334 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0324_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 324 10 10, g32p_row08_traceSegment_097_0324_0010, g32p_row08_traceSegment_097_0334_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0344_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 344 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0354_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 354 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0344_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 344 10 10, g32p_row08_traceSegment_097_0344_0010, g32p_row08_traceSegment_097_0354_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0324_0040 : g32p_coeffSegment g32p_row08_traceSegment_097 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 324 20 20, g32p_row08_traceSegment_097_0324_0020, g32p_row08_traceSegment_097_0344_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0364_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 364 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0374_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 374 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0364_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 364 10 10, g32p_row08_traceSegment_097_0364_0010, g32p_row08_traceSegment_097_0374_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0384_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 384 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0394_0011 : g32p_coeffSegment g32p_row08_traceSegment_097 394 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0384_0021 : g32p_coeffSegment g32p_row08_traceSegment_097 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 384 10 11, g32p_row08_traceSegment_097_0384_0010, g32p_row08_traceSegment_097_0394_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0364_0041 : g32p_coeffSegment g32p_row08_traceSegment_097 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 364 20 21, g32p_row08_traceSegment_097_0364_0020, g32p_row08_traceSegment_097_0384_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0324_0081 : g32p_coeffSegment g32p_row08_traceSegment_097 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 324 40 41, g32p_row08_traceSegment_097_0324_0040, g32p_row08_traceSegment_097_0364_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0405_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 405 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0415_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 415 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0405_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 405 10 10, g32p_row08_traceSegment_097_0405_0010, g32p_row08_traceSegment_097_0415_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0425_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 425 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0435_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 435 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0425_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 425 10 10, g32p_row08_traceSegment_097_0425_0010, g32p_row08_traceSegment_097_0435_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0405_0040 : g32p_coeffSegment g32p_row08_traceSegment_097 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 405 20 20, g32p_row08_traceSegment_097_0405_0020, g32p_row08_traceSegment_097_0425_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0445_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 445 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0455_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 455 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0445_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 445 10 10, g32p_row08_traceSegment_097_0445_0010, g32p_row08_traceSegment_097_0455_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0465_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 465 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0475_0011 : g32p_coeffSegment g32p_row08_traceSegment_097 475 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0465_0021 : g32p_coeffSegment g32p_row08_traceSegment_097 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 465 10 11, g32p_row08_traceSegment_097_0465_0010, g32p_row08_traceSegment_097_0475_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0445_0041 : g32p_coeffSegment g32p_row08_traceSegment_097 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 445 20 21, g32p_row08_traceSegment_097_0445_0020, g32p_row08_traceSegment_097_0465_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0405_0081 : g32p_coeffSegment g32p_row08_traceSegment_097 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 405 40 41, g32p_row08_traceSegment_097_0405_0040, g32p_row08_traceSegment_097_0445_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0324_0162 : g32p_coeffSegment g32p_row08_traceSegment_097 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 324 81 81, g32p_row08_traceSegment_097_0324_0081, g32p_row08_traceSegment_097_0405_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0486_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 486 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0496_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 496 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0486_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 486 10 10, g32p_row08_traceSegment_097_0486_0010, g32p_row08_traceSegment_097_0496_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0506_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 506 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0516_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 516 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0506_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 506 10 10, g32p_row08_traceSegment_097_0506_0010, g32p_row08_traceSegment_097_0516_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0486_0040 : g32p_coeffSegment g32p_row08_traceSegment_097 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 486 20 20, g32p_row08_traceSegment_097_0486_0020, g32p_row08_traceSegment_097_0506_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0526_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 526 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0536_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 536 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0526_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 526 10 10, g32p_row08_traceSegment_097_0526_0010, g32p_row08_traceSegment_097_0536_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0546_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 546 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0556_0011 : g32p_coeffSegment g32p_row08_traceSegment_097 556 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0546_0021 : g32p_coeffSegment g32p_row08_traceSegment_097 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 546 10 11, g32p_row08_traceSegment_097_0546_0010, g32p_row08_traceSegment_097_0556_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0526_0041 : g32p_coeffSegment g32p_row08_traceSegment_097 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 526 20 21, g32p_row08_traceSegment_097_0526_0020, g32p_row08_traceSegment_097_0546_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0486_0081 : g32p_coeffSegment g32p_row08_traceSegment_097 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 486 40 41, g32p_row08_traceSegment_097_0486_0040, g32p_row08_traceSegment_097_0526_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0567_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 567 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0577_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 577 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0567_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 567 10 10, g32p_row08_traceSegment_097_0567_0010, g32p_row08_traceSegment_097_0577_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0587_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 587 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0597_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 597 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0587_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 587 10 10, g32p_row08_traceSegment_097_0587_0010, g32p_row08_traceSegment_097_0597_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0567_0040 : g32p_coeffSegment g32p_row08_traceSegment_097 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 567 20 20, g32p_row08_traceSegment_097_0567_0020, g32p_row08_traceSegment_097_0587_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0607_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 607 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0617_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 617 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0607_0020 : g32p_coeffSegment g32p_row08_traceSegment_097 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 607 10 10, g32p_row08_traceSegment_097_0607_0010, g32p_row08_traceSegment_097_0617_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0627_0010 : g32p_coeffSegment g32p_row08_traceSegment_097 627 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0637_0011 : g32p_coeffSegment g32p_row08_traceSegment_097 637 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_097_0627_0021 : g32p_coeffSegment g32p_row08_traceSegment_097 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 627 10 11, g32p_row08_traceSegment_097_0627_0010, g32p_row08_traceSegment_097_0637_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0607_0041 : g32p_coeffSegment g32p_row08_traceSegment_097 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 607 20 21, g32p_row08_traceSegment_097_0607_0020, g32p_row08_traceSegment_097_0627_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0567_0081 : g32p_coeffSegment g32p_row08_traceSegment_097 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 567 40 41, g32p_row08_traceSegment_097_0567_0040, g32p_row08_traceSegment_097_0607_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0486_0162 : g32p_coeffSegment g32p_row08_traceSegment_097 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 486 81 81, g32p_row08_traceSegment_097_0486_0081, g32p_row08_traceSegment_097_0567_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0324_0324 : g32p_coeffSegment g32p_row08_traceSegment_097 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 324 162 162, g32p_row08_traceSegment_097_0324_0162, g32p_row08_traceSegment_097_0486_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_097_0000_0648 : g32p_coeffSegment g32p_row08_traceSegment_097 0 648 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_097 0 324 324, g32p_row08_traceSegment_097_0000_0324, g32p_row08_traceSegment_097_0324_0324]
  decide +kernel

theorem g32p_row08_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 97 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row08_traceSegment_097_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row08_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 84) 6
      (g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 84) (g32p_literalTraceValue 7 84)
      [1, -1, 1] [] = true := by
  rw [g32p_row08_traceCoefficients_084]
  decide +kernel

theorem g32p_row08_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 87) 6
      (g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 87) (g32p_literalTraceValue 7 87)
      [1, -1, 1] [15552, 15552, 15552] = true := by
  rw [g32p_row08_traceCoefficients_087]
  decide +kernel

theorem g32p_row08_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 88) 6
      (g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 88) (g32p_literalTraceValue 7 88)
      [1, -1, 1] [15552, 15552, 15552] = true := by
  rw [g32p_row08_traceCoefficients_088]
  decide +kernel

theorem g32p_row08_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 92) 6
      (g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 92) (g32p_literalTraceValue 7 92)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row08_traceCoefficients_092]
  decide +kernel

theorem g32p_row08_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 93) 6
      (g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 93) (g32p_literalTraceValue 7 93)
      [1, -1, 1] [15552, 15552, 15552] = true := by
  rw [g32p_row08_traceCoefficients_093]
  decide +kernel

theorem g32p_row08_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 95) 6
      (g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 95) (g32p_literalTraceValue 7 95)
      [1, -1, 1] [] = true := by
  rw [g32p_row08_traceCoefficients_095]
  decide +kernel

theorem g32p_row08_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 96) (g32p_literalTraceValue 7 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row08_traceCoefficients_096]
  decide +kernel

theorem g32p_row08_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 97) (g32p_literalTraceValue 7 97)
      [1, -1, 1] [] = true := by
  rw [g32p_row08_traceCoefficients_097]
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

private def g32p_row08_traceSegment_098 (k : ℕ) : List ℤ :=
  if g32p_row08_supplierClassifier (Fin.ofNat 648 k) = 98 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row08_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row08_traceSegment_098_0000_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 0 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0010_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 10 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0000_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 0 10 10, g32p_row08_traceSegment_098_0000_0010, g32p_row08_traceSegment_098_0010_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0020_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 20 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0030_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 30 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0020_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 20 10 10, g32p_row08_traceSegment_098_0020_0010, g32p_row08_traceSegment_098_0030_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0000_0040 : g32p_coeffSegment g32p_row08_traceSegment_098 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 0 20 20, g32p_row08_traceSegment_098_0000_0020, g32p_row08_traceSegment_098_0020_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0040_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 40 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0050_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 50 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0040_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 40 10 10, g32p_row08_traceSegment_098_0040_0010, g32p_row08_traceSegment_098_0050_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0060_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 60 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0070_0011 : g32p_coeffSegment g32p_row08_traceSegment_098 70 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0060_0021 : g32p_coeffSegment g32p_row08_traceSegment_098 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 60 10 11, g32p_row08_traceSegment_098_0060_0010, g32p_row08_traceSegment_098_0070_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0040_0041 : g32p_coeffSegment g32p_row08_traceSegment_098 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 40 20 21, g32p_row08_traceSegment_098_0040_0020, g32p_row08_traceSegment_098_0060_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0000_0081 : g32p_coeffSegment g32p_row08_traceSegment_098 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 0 40 41, g32p_row08_traceSegment_098_0000_0040, g32p_row08_traceSegment_098_0040_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0081_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 81 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0091_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 91 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0081_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 81 10 10, g32p_row08_traceSegment_098_0081_0010, g32p_row08_traceSegment_098_0091_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0101_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 101 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0111_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 111 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0101_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 101 10 10, g32p_row08_traceSegment_098_0101_0010, g32p_row08_traceSegment_098_0111_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0081_0040 : g32p_coeffSegment g32p_row08_traceSegment_098 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 81 20 20, g32p_row08_traceSegment_098_0081_0020, g32p_row08_traceSegment_098_0101_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0121_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 121 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0131_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 131 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0121_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 121 10 10, g32p_row08_traceSegment_098_0121_0010, g32p_row08_traceSegment_098_0131_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0141_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 141 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0151_0011 : g32p_coeffSegment g32p_row08_traceSegment_098 151 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0141_0021 : g32p_coeffSegment g32p_row08_traceSegment_098 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 141 10 11, g32p_row08_traceSegment_098_0141_0010, g32p_row08_traceSegment_098_0151_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0121_0041 : g32p_coeffSegment g32p_row08_traceSegment_098 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 121 20 21, g32p_row08_traceSegment_098_0121_0020, g32p_row08_traceSegment_098_0141_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0081_0081 : g32p_coeffSegment g32p_row08_traceSegment_098 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 81 40 41, g32p_row08_traceSegment_098_0081_0040, g32p_row08_traceSegment_098_0121_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0000_0162 : g32p_coeffSegment g32p_row08_traceSegment_098 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 0 81 81, g32p_row08_traceSegment_098_0000_0081, g32p_row08_traceSegment_098_0081_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0162_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 162 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0172_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 172 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0162_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 162 10 10, g32p_row08_traceSegment_098_0162_0010, g32p_row08_traceSegment_098_0172_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0182_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 182 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0192_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 192 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0182_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 182 10 10, g32p_row08_traceSegment_098_0182_0010, g32p_row08_traceSegment_098_0192_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0162_0040 : g32p_coeffSegment g32p_row08_traceSegment_098 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 162 20 20, g32p_row08_traceSegment_098_0162_0020, g32p_row08_traceSegment_098_0182_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0202_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 202 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0212_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 212 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0202_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 202 10 10, g32p_row08_traceSegment_098_0202_0010, g32p_row08_traceSegment_098_0212_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0222_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 222 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0232_0011 : g32p_coeffSegment g32p_row08_traceSegment_098 232 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0222_0021 : g32p_coeffSegment g32p_row08_traceSegment_098 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 222 10 11, g32p_row08_traceSegment_098_0222_0010, g32p_row08_traceSegment_098_0232_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0202_0041 : g32p_coeffSegment g32p_row08_traceSegment_098 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 202 20 21, g32p_row08_traceSegment_098_0202_0020, g32p_row08_traceSegment_098_0222_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0162_0081 : g32p_coeffSegment g32p_row08_traceSegment_098 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 162 40 41, g32p_row08_traceSegment_098_0162_0040, g32p_row08_traceSegment_098_0202_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0243_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 243 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0253_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 253 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0243_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 243 10 10, g32p_row08_traceSegment_098_0243_0010, g32p_row08_traceSegment_098_0253_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0263_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 263 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0273_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 273 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0263_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 263 10 10, g32p_row08_traceSegment_098_0263_0010, g32p_row08_traceSegment_098_0273_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0243_0040 : g32p_coeffSegment g32p_row08_traceSegment_098 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 243 20 20, g32p_row08_traceSegment_098_0243_0020, g32p_row08_traceSegment_098_0263_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0283_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 283 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0293_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 293 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0283_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 283 10 10, g32p_row08_traceSegment_098_0283_0010, g32p_row08_traceSegment_098_0293_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0303_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 303 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0313_0011 : g32p_coeffSegment g32p_row08_traceSegment_098 313 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0303_0021 : g32p_coeffSegment g32p_row08_traceSegment_098 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 303 10 11, g32p_row08_traceSegment_098_0303_0010, g32p_row08_traceSegment_098_0313_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0283_0041 : g32p_coeffSegment g32p_row08_traceSegment_098 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 283 20 21, g32p_row08_traceSegment_098_0283_0020, g32p_row08_traceSegment_098_0303_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0243_0081 : g32p_coeffSegment g32p_row08_traceSegment_098 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 243 40 41, g32p_row08_traceSegment_098_0243_0040, g32p_row08_traceSegment_098_0283_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0162_0162 : g32p_coeffSegment g32p_row08_traceSegment_098 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 162 81 81, g32p_row08_traceSegment_098_0162_0081, g32p_row08_traceSegment_098_0243_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0000_0324 : g32p_coeffSegment g32p_row08_traceSegment_098 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 0 162 162, g32p_row08_traceSegment_098_0000_0162, g32p_row08_traceSegment_098_0162_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0324_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 324 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0334_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 334 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0324_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 324 10 10, g32p_row08_traceSegment_098_0324_0010, g32p_row08_traceSegment_098_0334_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0344_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 344 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0354_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 354 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0344_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 344 10 10, g32p_row08_traceSegment_098_0344_0010, g32p_row08_traceSegment_098_0354_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0324_0040 : g32p_coeffSegment g32p_row08_traceSegment_098 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 324 20 20, g32p_row08_traceSegment_098_0324_0020, g32p_row08_traceSegment_098_0344_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0364_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 364 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0374_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 374 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0364_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 364 10 10, g32p_row08_traceSegment_098_0364_0010, g32p_row08_traceSegment_098_0374_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0384_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 384 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0394_0011 : g32p_coeffSegment g32p_row08_traceSegment_098 394 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0384_0021 : g32p_coeffSegment g32p_row08_traceSegment_098 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 384 10 11, g32p_row08_traceSegment_098_0384_0010, g32p_row08_traceSegment_098_0394_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0364_0041 : g32p_coeffSegment g32p_row08_traceSegment_098 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 364 20 21, g32p_row08_traceSegment_098_0364_0020, g32p_row08_traceSegment_098_0384_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0324_0081 : g32p_coeffSegment g32p_row08_traceSegment_098 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 324 40 41, g32p_row08_traceSegment_098_0324_0040, g32p_row08_traceSegment_098_0364_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0405_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 405 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0415_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 415 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0405_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 405 10 10, g32p_row08_traceSegment_098_0405_0010, g32p_row08_traceSegment_098_0415_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0425_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 425 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0435_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 435 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0425_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 425 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 425 10 10, g32p_row08_traceSegment_098_0425_0010, g32p_row08_traceSegment_098_0435_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0405_0040 : g32p_coeffSegment g32p_row08_traceSegment_098 405 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 405 20 20, g32p_row08_traceSegment_098_0405_0020, g32p_row08_traceSegment_098_0425_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0445_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 445 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0455_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 455 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0445_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 445 10 10, g32p_row08_traceSegment_098_0445_0010, g32p_row08_traceSegment_098_0455_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0465_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 465 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0475_0011 : g32p_coeffSegment g32p_row08_traceSegment_098 475 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0465_0021 : g32p_coeffSegment g32p_row08_traceSegment_098 465 21 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 465 10 11, g32p_row08_traceSegment_098_0465_0010, g32p_row08_traceSegment_098_0475_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0445_0041 : g32p_coeffSegment g32p_row08_traceSegment_098 445 41 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 445 20 21, g32p_row08_traceSegment_098_0445_0020, g32p_row08_traceSegment_098_0465_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0405_0081 : g32p_coeffSegment g32p_row08_traceSegment_098 405 81 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 405 40 41, g32p_row08_traceSegment_098_0405_0040, g32p_row08_traceSegment_098_0445_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0324_0162 : g32p_coeffSegment g32p_row08_traceSegment_098 324 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 324 81 81, g32p_row08_traceSegment_098_0324_0081, g32p_row08_traceSegment_098_0405_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0486_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 486 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0496_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 496 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0486_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 486 10 10, g32p_row08_traceSegment_098_0486_0010, g32p_row08_traceSegment_098_0496_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0506_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 506 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0516_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 516 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0506_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 506 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 506 10 10, g32p_row08_traceSegment_098_0506_0010, g32p_row08_traceSegment_098_0516_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0486_0040 : g32p_coeffSegment g32p_row08_traceSegment_098 486 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 486 20 20, g32p_row08_traceSegment_098_0486_0020, g32p_row08_traceSegment_098_0506_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0526_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 526 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0536_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 536 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0526_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 526 10 10, g32p_row08_traceSegment_098_0526_0010, g32p_row08_traceSegment_098_0536_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0546_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 546 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0556_0011 : g32p_coeffSegment g32p_row08_traceSegment_098 556 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0546_0021 : g32p_coeffSegment g32p_row08_traceSegment_098 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 546 10 11, g32p_row08_traceSegment_098_0546_0010, g32p_row08_traceSegment_098_0556_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0526_0041 : g32p_coeffSegment g32p_row08_traceSegment_098 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 526 20 21, g32p_row08_traceSegment_098_0526_0020, g32p_row08_traceSegment_098_0546_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0486_0081 : g32p_coeffSegment g32p_row08_traceSegment_098 486 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 486 40 41, g32p_row08_traceSegment_098_0486_0040, g32p_row08_traceSegment_098_0526_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0567_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 567 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0577_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 577 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0567_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 567 10 10, g32p_row08_traceSegment_098_0567_0010, g32p_row08_traceSegment_098_0577_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0587_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 587 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0597_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 597 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0587_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 587 10 10, g32p_row08_traceSegment_098_0587_0010, g32p_row08_traceSegment_098_0597_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0567_0040 : g32p_coeffSegment g32p_row08_traceSegment_098 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 567 20 20, g32p_row08_traceSegment_098_0567_0020, g32p_row08_traceSegment_098_0587_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0607_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 607 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0617_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 617 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0607_0020 : g32p_coeffSegment g32p_row08_traceSegment_098 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 607 10 10, g32p_row08_traceSegment_098_0607_0010, g32p_row08_traceSegment_098_0617_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0627_0010 : g32p_coeffSegment g32p_row08_traceSegment_098 627 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0637_0011 : g32p_coeffSegment g32p_row08_traceSegment_098 637 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_098_0627_0021 : g32p_coeffSegment g32p_row08_traceSegment_098 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 627 10 11, g32p_row08_traceSegment_098_0627_0010, g32p_row08_traceSegment_098_0637_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0607_0041 : g32p_coeffSegment g32p_row08_traceSegment_098 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 607 20 21, g32p_row08_traceSegment_098_0607_0020, g32p_row08_traceSegment_098_0627_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0567_0081 : g32p_coeffSegment g32p_row08_traceSegment_098 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 567 40 41, g32p_row08_traceSegment_098_0567_0040, g32p_row08_traceSegment_098_0607_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0486_0162 : g32p_coeffSegment g32p_row08_traceSegment_098 486 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 486 81 81, g32p_row08_traceSegment_098_0486_0081, g32p_row08_traceSegment_098_0567_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0324_0324 : g32p_coeffSegment g32p_row08_traceSegment_098 324 324 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 324 162 162, g32p_row08_traceSegment_098_0324_0162, g32p_row08_traceSegment_098_0486_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_098_0000_0648 : g32p_coeffSegment g32p_row08_traceSegment_098 0 648 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_098 0 324 324, g32p_row08_traceSegment_098_0000_0324, g32p_row08_traceSegment_098_0324_0324]
  decide +kernel

theorem g32p_row08_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 98 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row08_traceSegment_098_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row08_traceSegment_099 (k : ℕ) : List ℤ :=
  if g32p_row08_supplierClassifier (Fin.ofNat 648 k) = 99 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row08_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row08_traceSegment_099_0000_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 0 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0010_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 10 10 = [1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0000_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 0 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 0 10 10, g32p_row08_traceSegment_099_0000_0010, g32p_row08_traceSegment_099_0010_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0020_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 20 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0030_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 30 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0020_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 20 10 10, g32p_row08_traceSegment_099_0020_0010, g32p_row08_traceSegment_099_0030_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0000_0040 : g32p_coeffSegment g32p_row08_traceSegment_099 0 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 0 20 20, g32p_row08_traceSegment_099_0000_0020, g32p_row08_traceSegment_099_0020_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0040_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 40 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0050_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 50 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0040_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 40 10 10, g32p_row08_traceSegment_099_0040_0010, g32p_row08_traceSegment_099_0050_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0060_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 60 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0070_0011 : g32p_coeffSegment g32p_row08_traceSegment_099 70 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0060_0021 : g32p_coeffSegment g32p_row08_traceSegment_099 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 60 10 11, g32p_row08_traceSegment_099_0060_0010, g32p_row08_traceSegment_099_0070_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0040_0041 : g32p_coeffSegment g32p_row08_traceSegment_099 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 40 20 21, g32p_row08_traceSegment_099_0040_0020, g32p_row08_traceSegment_099_0060_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0000_0081 : g32p_coeffSegment g32p_row08_traceSegment_099 0 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 0 40 41, g32p_row08_traceSegment_099_0000_0040, g32p_row08_traceSegment_099_0040_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0081_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 81 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0091_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 91 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0081_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 81 10 10, g32p_row08_traceSegment_099_0081_0010, g32p_row08_traceSegment_099_0091_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0101_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 101 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0111_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 111 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0101_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 101 10 10, g32p_row08_traceSegment_099_0101_0010, g32p_row08_traceSegment_099_0111_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0081_0040 : g32p_coeffSegment g32p_row08_traceSegment_099 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 81 20 20, g32p_row08_traceSegment_099_0081_0020, g32p_row08_traceSegment_099_0101_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0121_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 121 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0131_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 131 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0121_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 121 10 10, g32p_row08_traceSegment_099_0121_0010, g32p_row08_traceSegment_099_0131_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0141_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 141 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0151_0011 : g32p_coeffSegment g32p_row08_traceSegment_099 151 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0141_0021 : g32p_coeffSegment g32p_row08_traceSegment_099 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 141 10 11, g32p_row08_traceSegment_099_0141_0010, g32p_row08_traceSegment_099_0151_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0121_0041 : g32p_coeffSegment g32p_row08_traceSegment_099 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 121 20 21, g32p_row08_traceSegment_099_0121_0020, g32p_row08_traceSegment_099_0141_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0081_0081 : g32p_coeffSegment g32p_row08_traceSegment_099 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 81 40 41, g32p_row08_traceSegment_099_0081_0040, g32p_row08_traceSegment_099_0121_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0000_0162 : g32p_coeffSegment g32p_row08_traceSegment_099 0 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 0 81 81, g32p_row08_traceSegment_099_0000_0081, g32p_row08_traceSegment_099_0081_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0162_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 162 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0172_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 172 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0162_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 162 10 10, g32p_row08_traceSegment_099_0162_0010, g32p_row08_traceSegment_099_0172_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0182_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 182 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0192_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 192 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0182_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 182 10 10, g32p_row08_traceSegment_099_0182_0010, g32p_row08_traceSegment_099_0192_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0162_0040 : g32p_coeffSegment g32p_row08_traceSegment_099 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 162 20 20, g32p_row08_traceSegment_099_0162_0020, g32p_row08_traceSegment_099_0182_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0202_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 202 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0212_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 212 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0202_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 202 10 10, g32p_row08_traceSegment_099_0202_0010, g32p_row08_traceSegment_099_0212_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0222_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 222 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0232_0011 : g32p_coeffSegment g32p_row08_traceSegment_099 232 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0222_0021 : g32p_coeffSegment g32p_row08_traceSegment_099 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 222 10 11, g32p_row08_traceSegment_099_0222_0010, g32p_row08_traceSegment_099_0232_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0202_0041 : g32p_coeffSegment g32p_row08_traceSegment_099 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 202 20 21, g32p_row08_traceSegment_099_0202_0020, g32p_row08_traceSegment_099_0222_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0162_0081 : g32p_coeffSegment g32p_row08_traceSegment_099 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 162 40 41, g32p_row08_traceSegment_099_0162_0040, g32p_row08_traceSegment_099_0202_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0243_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 243 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0253_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 253 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0243_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 243 10 10, g32p_row08_traceSegment_099_0243_0010, g32p_row08_traceSegment_099_0253_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0263_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 263 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0273_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 273 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0263_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 263 10 10, g32p_row08_traceSegment_099_0263_0010, g32p_row08_traceSegment_099_0273_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0243_0040 : g32p_coeffSegment g32p_row08_traceSegment_099 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 243 20 20, g32p_row08_traceSegment_099_0243_0020, g32p_row08_traceSegment_099_0263_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0283_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 283 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0293_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 293 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0283_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 283 10 10, g32p_row08_traceSegment_099_0283_0010, g32p_row08_traceSegment_099_0293_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0303_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 303 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0313_0011 : g32p_coeffSegment g32p_row08_traceSegment_099 313 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0303_0021 : g32p_coeffSegment g32p_row08_traceSegment_099 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 303 10 11, g32p_row08_traceSegment_099_0303_0010, g32p_row08_traceSegment_099_0313_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0283_0041 : g32p_coeffSegment g32p_row08_traceSegment_099 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 283 20 21, g32p_row08_traceSegment_099_0283_0020, g32p_row08_traceSegment_099_0303_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0243_0081 : g32p_coeffSegment g32p_row08_traceSegment_099 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 243 40 41, g32p_row08_traceSegment_099_0243_0040, g32p_row08_traceSegment_099_0283_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0162_0162 : g32p_coeffSegment g32p_row08_traceSegment_099 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 162 81 81, g32p_row08_traceSegment_099_0162_0081, g32p_row08_traceSegment_099_0243_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0000_0324 : g32p_coeffSegment g32p_row08_traceSegment_099 0 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 0 162 162, g32p_row08_traceSegment_099_0000_0162, g32p_row08_traceSegment_099_0162_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0324_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 324 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0334_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 334 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0324_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 324 10 10, g32p_row08_traceSegment_099_0324_0010, g32p_row08_traceSegment_099_0334_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0344_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 344 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0354_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 354 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0344_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 344 10 10, g32p_row08_traceSegment_099_0344_0010, g32p_row08_traceSegment_099_0354_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0324_0040 : g32p_coeffSegment g32p_row08_traceSegment_099 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 324 20 20, g32p_row08_traceSegment_099_0324_0020, g32p_row08_traceSegment_099_0344_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0364_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 364 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0374_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 374 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0364_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 364 10 10, g32p_row08_traceSegment_099_0364_0010, g32p_row08_traceSegment_099_0374_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0384_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 384 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0394_0011 : g32p_coeffSegment g32p_row08_traceSegment_099 394 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0384_0021 : g32p_coeffSegment g32p_row08_traceSegment_099 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 384 10 11, g32p_row08_traceSegment_099_0384_0010, g32p_row08_traceSegment_099_0394_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0364_0041 : g32p_coeffSegment g32p_row08_traceSegment_099 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 364 20 21, g32p_row08_traceSegment_099_0364_0020, g32p_row08_traceSegment_099_0384_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0324_0081 : g32p_coeffSegment g32p_row08_traceSegment_099 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 324 40 41, g32p_row08_traceSegment_099_0324_0040, g32p_row08_traceSegment_099_0364_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0405_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 405 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0415_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 415 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0405_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 405 10 10, g32p_row08_traceSegment_099_0405_0010, g32p_row08_traceSegment_099_0415_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0425_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 425 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0435_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 435 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0425_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 425 10 10, g32p_row08_traceSegment_099_0425_0010, g32p_row08_traceSegment_099_0435_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0405_0040 : g32p_coeffSegment g32p_row08_traceSegment_099 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 405 20 20, g32p_row08_traceSegment_099_0405_0020, g32p_row08_traceSegment_099_0425_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0445_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 445 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0455_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 455 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0445_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 445 10 10, g32p_row08_traceSegment_099_0445_0010, g32p_row08_traceSegment_099_0455_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0465_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 465 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0475_0011 : g32p_coeffSegment g32p_row08_traceSegment_099 475 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0465_0021 : g32p_coeffSegment g32p_row08_traceSegment_099 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 465 10 11, g32p_row08_traceSegment_099_0465_0010, g32p_row08_traceSegment_099_0475_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0445_0041 : g32p_coeffSegment g32p_row08_traceSegment_099 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 445 20 21, g32p_row08_traceSegment_099_0445_0020, g32p_row08_traceSegment_099_0465_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0405_0081 : g32p_coeffSegment g32p_row08_traceSegment_099 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 405 40 41, g32p_row08_traceSegment_099_0405_0040, g32p_row08_traceSegment_099_0445_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0324_0162 : g32p_coeffSegment g32p_row08_traceSegment_099 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 324 81 81, g32p_row08_traceSegment_099_0324_0081, g32p_row08_traceSegment_099_0405_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0486_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 486 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0496_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 496 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0486_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 486 10 10, g32p_row08_traceSegment_099_0486_0010, g32p_row08_traceSegment_099_0496_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0506_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 506 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0516_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 516 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0506_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 506 10 10, g32p_row08_traceSegment_099_0506_0010, g32p_row08_traceSegment_099_0516_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0486_0040 : g32p_coeffSegment g32p_row08_traceSegment_099 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 486 20 20, g32p_row08_traceSegment_099_0486_0020, g32p_row08_traceSegment_099_0506_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0526_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 526 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0536_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 536 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0526_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 526 10 10, g32p_row08_traceSegment_099_0526_0010, g32p_row08_traceSegment_099_0536_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0546_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 546 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0556_0011 : g32p_coeffSegment g32p_row08_traceSegment_099 556 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0546_0021 : g32p_coeffSegment g32p_row08_traceSegment_099 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 546 10 11, g32p_row08_traceSegment_099_0546_0010, g32p_row08_traceSegment_099_0556_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0526_0041 : g32p_coeffSegment g32p_row08_traceSegment_099 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 526 20 21, g32p_row08_traceSegment_099_0526_0020, g32p_row08_traceSegment_099_0546_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0486_0081 : g32p_coeffSegment g32p_row08_traceSegment_099 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 486 40 41, g32p_row08_traceSegment_099_0486_0040, g32p_row08_traceSegment_099_0526_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0567_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 567 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0577_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 577 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0567_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 567 10 10, g32p_row08_traceSegment_099_0567_0010, g32p_row08_traceSegment_099_0577_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0587_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 587 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0597_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 597 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0587_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 587 10 10, g32p_row08_traceSegment_099_0587_0010, g32p_row08_traceSegment_099_0597_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0567_0040 : g32p_coeffSegment g32p_row08_traceSegment_099 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 567 20 20, g32p_row08_traceSegment_099_0567_0020, g32p_row08_traceSegment_099_0587_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0607_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 607 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0617_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 617 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0607_0020 : g32p_coeffSegment g32p_row08_traceSegment_099 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 607 10 10, g32p_row08_traceSegment_099_0607_0010, g32p_row08_traceSegment_099_0617_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0627_0010 : g32p_coeffSegment g32p_row08_traceSegment_099 627 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0637_0011 : g32p_coeffSegment g32p_row08_traceSegment_099 637 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_099_0627_0021 : g32p_coeffSegment g32p_row08_traceSegment_099 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 627 10 11, g32p_row08_traceSegment_099_0627_0010, g32p_row08_traceSegment_099_0637_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0607_0041 : g32p_coeffSegment g32p_row08_traceSegment_099 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 607 20 21, g32p_row08_traceSegment_099_0607_0020, g32p_row08_traceSegment_099_0627_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0567_0081 : g32p_coeffSegment g32p_row08_traceSegment_099 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 567 40 41, g32p_row08_traceSegment_099_0567_0040, g32p_row08_traceSegment_099_0607_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0486_0162 : g32p_coeffSegment g32p_row08_traceSegment_099 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 486 81 81, g32p_row08_traceSegment_099_0486_0081, g32p_row08_traceSegment_099_0567_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0324_0324 : g32p_coeffSegment g32p_row08_traceSegment_099 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 324 162 162, g32p_row08_traceSegment_099_0324_0162, g32p_row08_traceSegment_099_0486_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_099_0000_0648 : g32p_coeffSegment g32p_row08_traceSegment_099 0 648 = [1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_099 0 324 324, g32p_row08_traceSegment_099_0000_0324, g32p_row08_traceSegment_099_0324_0324]
  decide +kernel

theorem g32p_row08_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 99 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row08_traceSegment_099_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row08_traceSegment_100 (k : ℕ) : List ℤ :=
  if g32p_row08_supplierClassifier (Fin.ofNat 648 k) = 100 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row08_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row08_traceSegment_100_0000_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 0 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0010_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 10 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0000_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 0 10 10, g32p_row08_traceSegment_100_0000_0010, g32p_row08_traceSegment_100_0010_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0020_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 20 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0030_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 30 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0020_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 20 10 10, g32p_row08_traceSegment_100_0020_0010, g32p_row08_traceSegment_100_0030_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0000_0040 : g32p_coeffSegment g32p_row08_traceSegment_100 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 0 20 20, g32p_row08_traceSegment_100_0000_0020, g32p_row08_traceSegment_100_0020_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0040_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 40 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0050_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 50 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0040_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 40 10 10, g32p_row08_traceSegment_100_0040_0010, g32p_row08_traceSegment_100_0050_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0060_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 60 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0070_0011 : g32p_coeffSegment g32p_row08_traceSegment_100 70 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0060_0021 : g32p_coeffSegment g32p_row08_traceSegment_100 60 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 60 10 11, g32p_row08_traceSegment_100_0060_0010, g32p_row08_traceSegment_100_0070_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0040_0041 : g32p_coeffSegment g32p_row08_traceSegment_100 40 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 40 20 21, g32p_row08_traceSegment_100_0040_0020, g32p_row08_traceSegment_100_0060_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0000_0081 : g32p_coeffSegment g32p_row08_traceSegment_100 0 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 0 40 41, g32p_row08_traceSegment_100_0000_0040, g32p_row08_traceSegment_100_0040_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0081_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 81 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0091_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 91 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0081_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 81 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 81 10 10, g32p_row08_traceSegment_100_0081_0010, g32p_row08_traceSegment_100_0091_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0101_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 101 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0111_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 111 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0101_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 101 10 10, g32p_row08_traceSegment_100_0101_0010, g32p_row08_traceSegment_100_0111_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0081_0040 : g32p_coeffSegment g32p_row08_traceSegment_100 81 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 81 20 20, g32p_row08_traceSegment_100_0081_0020, g32p_row08_traceSegment_100_0101_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0121_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 121 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0131_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 131 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0121_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 121 10 10, g32p_row08_traceSegment_100_0121_0010, g32p_row08_traceSegment_100_0131_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0141_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 141 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0151_0011 : g32p_coeffSegment g32p_row08_traceSegment_100 151 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0141_0021 : g32p_coeffSegment g32p_row08_traceSegment_100 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 141 10 11, g32p_row08_traceSegment_100_0141_0010, g32p_row08_traceSegment_100_0151_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0121_0041 : g32p_coeffSegment g32p_row08_traceSegment_100 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 121 20 21, g32p_row08_traceSegment_100_0121_0020, g32p_row08_traceSegment_100_0141_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0081_0081 : g32p_coeffSegment g32p_row08_traceSegment_100 81 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 81 40 41, g32p_row08_traceSegment_100_0081_0040, g32p_row08_traceSegment_100_0121_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0000_0162 : g32p_coeffSegment g32p_row08_traceSegment_100 0 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 0 81 81, g32p_row08_traceSegment_100_0000_0081, g32p_row08_traceSegment_100_0081_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0162_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 162 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0172_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 172 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0162_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 162 10 10, g32p_row08_traceSegment_100_0162_0010, g32p_row08_traceSegment_100_0172_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0182_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 182 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0192_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 192 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0182_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 182 10 10, g32p_row08_traceSegment_100_0182_0010, g32p_row08_traceSegment_100_0192_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0162_0040 : g32p_coeffSegment g32p_row08_traceSegment_100 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 162 20 20, g32p_row08_traceSegment_100_0162_0020, g32p_row08_traceSegment_100_0182_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0202_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 202 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0212_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 212 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0202_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 202 10 10, g32p_row08_traceSegment_100_0202_0010, g32p_row08_traceSegment_100_0212_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0222_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 222 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0232_0011 : g32p_coeffSegment g32p_row08_traceSegment_100 232 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0222_0021 : g32p_coeffSegment g32p_row08_traceSegment_100 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 222 10 11, g32p_row08_traceSegment_100_0222_0010, g32p_row08_traceSegment_100_0232_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0202_0041 : g32p_coeffSegment g32p_row08_traceSegment_100 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 202 20 21, g32p_row08_traceSegment_100_0202_0020, g32p_row08_traceSegment_100_0222_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0162_0081 : g32p_coeffSegment g32p_row08_traceSegment_100 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 162 40 41, g32p_row08_traceSegment_100_0162_0040, g32p_row08_traceSegment_100_0202_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0243_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 243 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0253_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 253 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0243_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 243 10 10, g32p_row08_traceSegment_100_0243_0010, g32p_row08_traceSegment_100_0253_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0263_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 263 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0273_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 273 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0263_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 263 10 10, g32p_row08_traceSegment_100_0263_0010, g32p_row08_traceSegment_100_0273_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0243_0040 : g32p_coeffSegment g32p_row08_traceSegment_100 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 243 20 20, g32p_row08_traceSegment_100_0243_0020, g32p_row08_traceSegment_100_0263_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0283_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 283 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0293_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 293 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0283_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 283 10 10, g32p_row08_traceSegment_100_0283_0010, g32p_row08_traceSegment_100_0293_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0303_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 303 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0313_0011 : g32p_coeffSegment g32p_row08_traceSegment_100 313 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0303_0021 : g32p_coeffSegment g32p_row08_traceSegment_100 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 303 10 11, g32p_row08_traceSegment_100_0303_0010, g32p_row08_traceSegment_100_0313_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0283_0041 : g32p_coeffSegment g32p_row08_traceSegment_100 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 283 20 21, g32p_row08_traceSegment_100_0283_0020, g32p_row08_traceSegment_100_0303_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0243_0081 : g32p_coeffSegment g32p_row08_traceSegment_100 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 243 40 41, g32p_row08_traceSegment_100_0243_0040, g32p_row08_traceSegment_100_0283_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0162_0162 : g32p_coeffSegment g32p_row08_traceSegment_100 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 162 81 81, g32p_row08_traceSegment_100_0162_0081, g32p_row08_traceSegment_100_0243_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0000_0324 : g32p_coeffSegment g32p_row08_traceSegment_100 0 324 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 0 162 162, g32p_row08_traceSegment_100_0000_0162, g32p_row08_traceSegment_100_0162_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0324_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 324 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0334_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 334 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0324_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 324 10 10, g32p_row08_traceSegment_100_0324_0010, g32p_row08_traceSegment_100_0334_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0344_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 344 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0354_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 354 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0344_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 344 10 10, g32p_row08_traceSegment_100_0344_0010, g32p_row08_traceSegment_100_0354_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0324_0040 : g32p_coeffSegment g32p_row08_traceSegment_100 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 324 20 20, g32p_row08_traceSegment_100_0324_0020, g32p_row08_traceSegment_100_0344_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0364_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 364 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0374_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 374 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0364_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 364 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 364 10 10, g32p_row08_traceSegment_100_0364_0010, g32p_row08_traceSegment_100_0374_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0384_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 384 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0394_0011 : g32p_coeffSegment g32p_row08_traceSegment_100 394 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0384_0021 : g32p_coeffSegment g32p_row08_traceSegment_100 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 384 10 11, g32p_row08_traceSegment_100_0384_0010, g32p_row08_traceSegment_100_0394_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0364_0041 : g32p_coeffSegment g32p_row08_traceSegment_100 364 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 364 20 21, g32p_row08_traceSegment_100_0364_0020, g32p_row08_traceSegment_100_0384_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0324_0081 : g32p_coeffSegment g32p_row08_traceSegment_100 324 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 324 40 41, g32p_row08_traceSegment_100_0324_0040, g32p_row08_traceSegment_100_0364_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0405_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 405 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0415_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 415 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0405_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 405 10 10, g32p_row08_traceSegment_100_0405_0010, g32p_row08_traceSegment_100_0415_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0425_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 425 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0435_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 435 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0425_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 425 10 10, g32p_row08_traceSegment_100_0425_0010, g32p_row08_traceSegment_100_0435_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0405_0040 : g32p_coeffSegment g32p_row08_traceSegment_100 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 405 20 20, g32p_row08_traceSegment_100_0405_0020, g32p_row08_traceSegment_100_0425_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0445_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 445 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0455_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 455 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0445_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 445 10 10, g32p_row08_traceSegment_100_0445_0010, g32p_row08_traceSegment_100_0455_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0465_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 465 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0475_0011 : g32p_coeffSegment g32p_row08_traceSegment_100 475 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0465_0021 : g32p_coeffSegment g32p_row08_traceSegment_100 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 465 10 11, g32p_row08_traceSegment_100_0465_0010, g32p_row08_traceSegment_100_0475_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0445_0041 : g32p_coeffSegment g32p_row08_traceSegment_100 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 445 20 21, g32p_row08_traceSegment_100_0445_0020, g32p_row08_traceSegment_100_0465_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0405_0081 : g32p_coeffSegment g32p_row08_traceSegment_100 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 405 40 41, g32p_row08_traceSegment_100_0405_0040, g32p_row08_traceSegment_100_0445_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0324_0162 : g32p_coeffSegment g32p_row08_traceSegment_100 324 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 324 81 81, g32p_row08_traceSegment_100_0324_0081, g32p_row08_traceSegment_100_0405_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0486_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 486 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0496_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 496 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0486_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 486 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 486 10 10, g32p_row08_traceSegment_100_0486_0010, g32p_row08_traceSegment_100_0496_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0506_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 506 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0516_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 516 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0506_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 506 10 10, g32p_row08_traceSegment_100_0506_0010, g32p_row08_traceSegment_100_0516_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0486_0040 : g32p_coeffSegment g32p_row08_traceSegment_100 486 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 486 20 20, g32p_row08_traceSegment_100_0486_0020, g32p_row08_traceSegment_100_0506_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0526_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 526 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0536_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 536 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0526_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 526 10 10, g32p_row08_traceSegment_100_0526_0010, g32p_row08_traceSegment_100_0536_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0546_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 546 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0556_0011 : g32p_coeffSegment g32p_row08_traceSegment_100 556 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0546_0021 : g32p_coeffSegment g32p_row08_traceSegment_100 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 546 10 11, g32p_row08_traceSegment_100_0546_0010, g32p_row08_traceSegment_100_0556_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0526_0041 : g32p_coeffSegment g32p_row08_traceSegment_100 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 526 20 21, g32p_row08_traceSegment_100_0526_0020, g32p_row08_traceSegment_100_0546_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0486_0081 : g32p_coeffSegment g32p_row08_traceSegment_100 486 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 486 40 41, g32p_row08_traceSegment_100_0486_0040, g32p_row08_traceSegment_100_0526_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0567_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 567 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0577_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 577 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0567_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 567 10 10, g32p_row08_traceSegment_100_0567_0010, g32p_row08_traceSegment_100_0577_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0587_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 587 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0597_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 597 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0587_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 587 10 10, g32p_row08_traceSegment_100_0587_0010, g32p_row08_traceSegment_100_0597_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0567_0040 : g32p_coeffSegment g32p_row08_traceSegment_100 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 567 20 20, g32p_row08_traceSegment_100_0567_0020, g32p_row08_traceSegment_100_0587_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0607_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 607 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0617_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 617 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0607_0020 : g32p_coeffSegment g32p_row08_traceSegment_100 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 607 10 10, g32p_row08_traceSegment_100_0607_0010, g32p_row08_traceSegment_100_0617_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0627_0010 : g32p_coeffSegment g32p_row08_traceSegment_100 627 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0637_0011 : g32p_coeffSegment g32p_row08_traceSegment_100 637 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_100_0627_0021 : g32p_coeffSegment g32p_row08_traceSegment_100 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 627 10 11, g32p_row08_traceSegment_100_0627_0010, g32p_row08_traceSegment_100_0637_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0607_0041 : g32p_coeffSegment g32p_row08_traceSegment_100 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 607 20 21, g32p_row08_traceSegment_100_0607_0020, g32p_row08_traceSegment_100_0627_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0567_0081 : g32p_coeffSegment g32p_row08_traceSegment_100 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 567 40 41, g32p_row08_traceSegment_100_0567_0040, g32p_row08_traceSegment_100_0607_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0486_0162 : g32p_coeffSegment g32p_row08_traceSegment_100 486 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 486 81 81, g32p_row08_traceSegment_100_0486_0081, g32p_row08_traceSegment_100_0567_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0324_0324 : g32p_coeffSegment g32p_row08_traceSegment_100 324 324 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 324 162 162, g32p_row08_traceSegment_100_0324_0162, g32p_row08_traceSegment_100_0486_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_100_0000_0648 : g32p_coeffSegment g32p_row08_traceSegment_100 0 648 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_100 0 324 324, g32p_row08_traceSegment_100_0000_0324, g32p_row08_traceSegment_100_0324_0324]
  decide +kernel

theorem g32p_row08_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 100 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row08_traceSegment_100_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row08_traceSegment_101 (k : ℕ) : List ℤ :=
  if g32p_row08_supplierClassifier (Fin.ofNat 648 k) = 101 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row08_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row08_traceSegment_101_0000_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 0 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0010_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 10 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0000_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 0 10 10, g32p_row08_traceSegment_101_0000_0010, g32p_row08_traceSegment_101_0010_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0020_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 20 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0030_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 30 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0020_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 20 10 10, g32p_row08_traceSegment_101_0020_0010, g32p_row08_traceSegment_101_0030_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0000_0040 : g32p_coeffSegment g32p_row08_traceSegment_101 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 0 20 20, g32p_row08_traceSegment_101_0000_0020, g32p_row08_traceSegment_101_0020_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0040_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 40 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0050_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 50 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0040_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 40 10 10, g32p_row08_traceSegment_101_0040_0010, g32p_row08_traceSegment_101_0050_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0060_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 60 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0070_0011 : g32p_coeffSegment g32p_row08_traceSegment_101 70 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0060_0021 : g32p_coeffSegment g32p_row08_traceSegment_101 60 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 60 10 11, g32p_row08_traceSegment_101_0060_0010, g32p_row08_traceSegment_101_0070_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0040_0041 : g32p_coeffSegment g32p_row08_traceSegment_101 40 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 40 20 21, g32p_row08_traceSegment_101_0040_0020, g32p_row08_traceSegment_101_0060_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0000_0081 : g32p_coeffSegment g32p_row08_traceSegment_101 0 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 0 40 41, g32p_row08_traceSegment_101_0000_0040, g32p_row08_traceSegment_101_0040_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0081_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 81 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0091_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 91 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0081_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 81 10 10, g32p_row08_traceSegment_101_0081_0010, g32p_row08_traceSegment_101_0091_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0101_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 101 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0111_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 111 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0101_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 101 10 10, g32p_row08_traceSegment_101_0101_0010, g32p_row08_traceSegment_101_0111_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0081_0040 : g32p_coeffSegment g32p_row08_traceSegment_101 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 81 20 20, g32p_row08_traceSegment_101_0081_0020, g32p_row08_traceSegment_101_0101_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0121_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 121 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0131_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 131 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0121_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 121 10 10, g32p_row08_traceSegment_101_0121_0010, g32p_row08_traceSegment_101_0131_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0141_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 141 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0151_0011 : g32p_coeffSegment g32p_row08_traceSegment_101 151 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0141_0021 : g32p_coeffSegment g32p_row08_traceSegment_101 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 141 10 11, g32p_row08_traceSegment_101_0141_0010, g32p_row08_traceSegment_101_0151_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0121_0041 : g32p_coeffSegment g32p_row08_traceSegment_101 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 121 20 21, g32p_row08_traceSegment_101_0121_0020, g32p_row08_traceSegment_101_0141_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0081_0081 : g32p_coeffSegment g32p_row08_traceSegment_101 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 81 40 41, g32p_row08_traceSegment_101_0081_0040, g32p_row08_traceSegment_101_0121_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0000_0162 : g32p_coeffSegment g32p_row08_traceSegment_101 0 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 0 81 81, g32p_row08_traceSegment_101_0000_0081, g32p_row08_traceSegment_101_0081_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0162_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 162 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0172_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 172 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0162_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 162 10 10, g32p_row08_traceSegment_101_0162_0010, g32p_row08_traceSegment_101_0172_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0182_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 182 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0192_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 192 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0182_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 182 10 10, g32p_row08_traceSegment_101_0182_0010, g32p_row08_traceSegment_101_0192_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0162_0040 : g32p_coeffSegment g32p_row08_traceSegment_101 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 162 20 20, g32p_row08_traceSegment_101_0162_0020, g32p_row08_traceSegment_101_0182_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0202_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 202 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0212_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 212 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0202_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 202 10 10, g32p_row08_traceSegment_101_0202_0010, g32p_row08_traceSegment_101_0212_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0222_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 222 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0232_0011 : g32p_coeffSegment g32p_row08_traceSegment_101 232 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0222_0021 : g32p_coeffSegment g32p_row08_traceSegment_101 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 222 10 11, g32p_row08_traceSegment_101_0222_0010, g32p_row08_traceSegment_101_0232_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0202_0041 : g32p_coeffSegment g32p_row08_traceSegment_101 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 202 20 21, g32p_row08_traceSegment_101_0202_0020, g32p_row08_traceSegment_101_0222_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0162_0081 : g32p_coeffSegment g32p_row08_traceSegment_101 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 162 40 41, g32p_row08_traceSegment_101_0162_0040, g32p_row08_traceSegment_101_0202_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0243_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 243 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0253_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 253 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0243_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 243 10 10, g32p_row08_traceSegment_101_0243_0010, g32p_row08_traceSegment_101_0253_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0263_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 263 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0273_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 273 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0263_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 263 10 10, g32p_row08_traceSegment_101_0263_0010, g32p_row08_traceSegment_101_0273_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0243_0040 : g32p_coeffSegment g32p_row08_traceSegment_101 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 243 20 20, g32p_row08_traceSegment_101_0243_0020, g32p_row08_traceSegment_101_0263_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0283_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 283 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0293_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 293 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0283_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 283 10 10, g32p_row08_traceSegment_101_0283_0010, g32p_row08_traceSegment_101_0293_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0303_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 303 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0313_0011 : g32p_coeffSegment g32p_row08_traceSegment_101 313 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0303_0021 : g32p_coeffSegment g32p_row08_traceSegment_101 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 303 10 11, g32p_row08_traceSegment_101_0303_0010, g32p_row08_traceSegment_101_0313_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0283_0041 : g32p_coeffSegment g32p_row08_traceSegment_101 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 283 20 21, g32p_row08_traceSegment_101_0283_0020, g32p_row08_traceSegment_101_0303_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0243_0081 : g32p_coeffSegment g32p_row08_traceSegment_101 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 243 40 41, g32p_row08_traceSegment_101_0243_0040, g32p_row08_traceSegment_101_0283_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0162_0162 : g32p_coeffSegment g32p_row08_traceSegment_101 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 162 81 81, g32p_row08_traceSegment_101_0162_0081, g32p_row08_traceSegment_101_0243_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0000_0324 : g32p_coeffSegment g32p_row08_traceSegment_101 0 324 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 0 162 162, g32p_row08_traceSegment_101_0000_0162, g32p_row08_traceSegment_101_0162_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0324_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 324 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0334_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 334 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0324_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 324 10 10, g32p_row08_traceSegment_101_0324_0010, g32p_row08_traceSegment_101_0334_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0344_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 344 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0354_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 354 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0344_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 344 10 10, g32p_row08_traceSegment_101_0344_0010, g32p_row08_traceSegment_101_0354_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0324_0040 : g32p_coeffSegment g32p_row08_traceSegment_101 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 324 20 20, g32p_row08_traceSegment_101_0324_0020, g32p_row08_traceSegment_101_0344_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0364_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 364 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0374_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 374 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0364_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 364 10 10, g32p_row08_traceSegment_101_0364_0010, g32p_row08_traceSegment_101_0374_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0384_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 384 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0394_0011 : g32p_coeffSegment g32p_row08_traceSegment_101 394 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0384_0021 : g32p_coeffSegment g32p_row08_traceSegment_101 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 384 10 11, g32p_row08_traceSegment_101_0384_0010, g32p_row08_traceSegment_101_0394_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0364_0041 : g32p_coeffSegment g32p_row08_traceSegment_101 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 364 20 21, g32p_row08_traceSegment_101_0364_0020, g32p_row08_traceSegment_101_0384_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0324_0081 : g32p_coeffSegment g32p_row08_traceSegment_101 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 324 40 41, g32p_row08_traceSegment_101_0324_0040, g32p_row08_traceSegment_101_0364_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0405_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 405 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0415_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 415 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0405_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 405 10 10, g32p_row08_traceSegment_101_0405_0010, g32p_row08_traceSegment_101_0415_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0425_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 425 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0435_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 435 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0425_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 425 10 10, g32p_row08_traceSegment_101_0425_0010, g32p_row08_traceSegment_101_0435_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0405_0040 : g32p_coeffSegment g32p_row08_traceSegment_101 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 405 20 20, g32p_row08_traceSegment_101_0405_0020, g32p_row08_traceSegment_101_0425_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0445_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 445 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0455_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 455 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0445_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 445 10 10, g32p_row08_traceSegment_101_0445_0010, g32p_row08_traceSegment_101_0455_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0465_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 465 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0475_0011 : g32p_coeffSegment g32p_row08_traceSegment_101 475 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0465_0021 : g32p_coeffSegment g32p_row08_traceSegment_101 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 465 10 11, g32p_row08_traceSegment_101_0465_0010, g32p_row08_traceSegment_101_0475_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0445_0041 : g32p_coeffSegment g32p_row08_traceSegment_101 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 445 20 21, g32p_row08_traceSegment_101_0445_0020, g32p_row08_traceSegment_101_0465_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0405_0081 : g32p_coeffSegment g32p_row08_traceSegment_101 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 405 40 41, g32p_row08_traceSegment_101_0405_0040, g32p_row08_traceSegment_101_0445_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0324_0162 : g32p_coeffSegment g32p_row08_traceSegment_101 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 324 81 81, g32p_row08_traceSegment_101_0324_0081, g32p_row08_traceSegment_101_0405_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0486_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 486 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0496_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 496 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0486_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 486 10 10, g32p_row08_traceSegment_101_0486_0010, g32p_row08_traceSegment_101_0496_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0506_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 506 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0516_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 516 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0506_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 506 10 10, g32p_row08_traceSegment_101_0506_0010, g32p_row08_traceSegment_101_0516_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0486_0040 : g32p_coeffSegment g32p_row08_traceSegment_101 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 486 20 20, g32p_row08_traceSegment_101_0486_0020, g32p_row08_traceSegment_101_0506_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0526_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 526 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0536_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 536 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0526_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 526 10 10, g32p_row08_traceSegment_101_0526_0010, g32p_row08_traceSegment_101_0536_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0546_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 546 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0556_0011 : g32p_coeffSegment g32p_row08_traceSegment_101 556 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0546_0021 : g32p_coeffSegment g32p_row08_traceSegment_101 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 546 10 11, g32p_row08_traceSegment_101_0546_0010, g32p_row08_traceSegment_101_0556_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0526_0041 : g32p_coeffSegment g32p_row08_traceSegment_101 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 526 20 21, g32p_row08_traceSegment_101_0526_0020, g32p_row08_traceSegment_101_0546_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0486_0081 : g32p_coeffSegment g32p_row08_traceSegment_101 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 486 40 41, g32p_row08_traceSegment_101_0486_0040, g32p_row08_traceSegment_101_0526_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0567_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 567 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0577_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 577 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0567_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 567 10 10, g32p_row08_traceSegment_101_0567_0010, g32p_row08_traceSegment_101_0577_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0587_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 587 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0597_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 597 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0587_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 587 10 10, g32p_row08_traceSegment_101_0587_0010, g32p_row08_traceSegment_101_0597_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0567_0040 : g32p_coeffSegment g32p_row08_traceSegment_101 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 567 20 20, g32p_row08_traceSegment_101_0567_0020, g32p_row08_traceSegment_101_0587_0020]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0607_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 607 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0617_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 617 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0607_0020 : g32p_coeffSegment g32p_row08_traceSegment_101 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 607 10 10, g32p_row08_traceSegment_101_0607_0010, g32p_row08_traceSegment_101_0617_0010]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0627_0010 : g32p_coeffSegment g32p_row08_traceSegment_101 627 10 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0637_0011 : g32p_coeffSegment g32p_row08_traceSegment_101 637 11 = [] := by
  decide +kernel

private theorem g32p_row08_traceSegment_101_0627_0021 : g32p_coeffSegment g32p_row08_traceSegment_101 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 627 10 11, g32p_row08_traceSegment_101_0627_0010, g32p_row08_traceSegment_101_0637_0011]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0607_0041 : g32p_coeffSegment g32p_row08_traceSegment_101 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 607 20 21, g32p_row08_traceSegment_101_0607_0020, g32p_row08_traceSegment_101_0627_0021]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0567_0081 : g32p_coeffSegment g32p_row08_traceSegment_101 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 567 40 41, g32p_row08_traceSegment_101_0567_0040, g32p_row08_traceSegment_101_0607_0041]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0486_0162 : g32p_coeffSegment g32p_row08_traceSegment_101 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 486 81 81, g32p_row08_traceSegment_101_0486_0081, g32p_row08_traceSegment_101_0567_0081]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0324_0324 : g32p_coeffSegment g32p_row08_traceSegment_101 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 324 162 162, g32p_row08_traceSegment_101_0324_0162, g32p_row08_traceSegment_101_0486_0162]
  decide +kernel

private theorem g32p_row08_traceSegment_101_0000_0648 : g32p_coeffSegment g32p_row08_traceSegment_101 0 648 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row08_traceSegment_101 0 324 324, g32p_row08_traceSegment_101_0000_0324, g32p_row08_traceSegment_101_0324_0324]
  decide +kernel

theorem g32p_row08_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 101 = [0, 0, 0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row08_traceSegment_101_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row08_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 98) 6
      (g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 98) (g32p_literalTraceValue 7 98)
      [1, -1, 1] [] = true := by
  rw [g32p_row08_traceCoefficients_098]
  decide +kernel

theorem g32p_row08_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 99) (g32p_literalTraceValue 7 99)
      [1, -1, 1] [] = true := by
  rw [g32p_row08_traceCoefficients_099]
  decide +kernel

theorem g32p_row08_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 100) 6
      (g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 100) (g32p_literalTraceValue 7 100)
      [1, -1, 1] [] = true := by
  rw [g32p_row08_traceCoefficients_100]
  decide +kernel

theorem g32p_row08_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) 101) (g32p_literalTraceValue 7 101)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row08_traceCoefficients_101]
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

def g32p_row08_generatorIndex : Fin 8 → Fin 408 :=
  ![7, 58, 109, 160, 218, 219, 320, 321]

theorem g32p_row08_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup06_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 7 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 7 g32p_row08_supplierClass
    g32p_row08_supplierClass_isConj g32p_supplierGroup06_support g32p_row08_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row08_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup06_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row08_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 7 c false (g32p_row08_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 7 c true (g32p_row08_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 7 c false (g32p_row08_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 7 c true (g32p_row08_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 7 c false (g32p_row08_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 7 c false (g32p_row08_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 7 c true (g32p_row08_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 7 c true (g32p_row08_coinduced_zero c hc true) 3

theorem g32p_row08_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup06_support →
      g32p_literalTraceValue (g32p_row08_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row08_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup06_support →
      g32p_literalTraceValue (g32p_row08_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row08_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup06_support →
      g32p_literalTraceValue (g32p_row08_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row08_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup06_support →
      g32p_literalTraceValue (g32p_row08_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row08_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup06_support →
      g32p_literalTraceValue (g32p_row08_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row08_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup06_support →
      g32p_literalTraceValue (g32p_row08_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row08_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup06_support →
      g32p_literalTraceValue (g32p_row08_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row08_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup06_support) :
    g32p_literalTraceValue (g32p_row08_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup06_support →
    g32p_literalTraceValue (g32p_row08_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row08_zeroTrace_block_00 r k
  · exact g32p_row08_zeroTrace_block_01 r k
  · exact g32p_row08_zeroTrace_block_02 r k
  · exact g32p_row08_zeroTrace_block_03 r k
  · exact g32p_row08_zeroTrace_block_04 r k
  · exact g32p_row08_zeroTrace_block_05 r k
  · exact g32p_row08_zeroTrace_block_06 r k

theorem g32p_row08_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup06_support) :
    (g32p_recordedInductionGenerators (g32p_row08_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row08_generatorIndex k) c) := by
  rw [g32p_row08_recordedGenerator_zero c hc k, g32p_row08_zeroTrace_arithmetic c k hc]
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

def g32p_row08_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [15552, 15552, 15552])) else (if i.val < 4 then [] else (if i.val < 5 then [3888, 3888, 3888] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [0, 0, 10368, 10368] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [2592, 2592] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else [-1296, 1296, 1296]))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [3888, 3888, 3888] else [])) else (if i.val < 36 then (if i.val < 35 then [-5184, 5184, 5184] else [3888, 3888, 3888]) else (if i.val < 37 then [] else [155520, 155520, 155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [0, 0, 2592, 2592])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [10368, 10368] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [15552, 15552, 15552] else [15552, 15552, 15552])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [3888, 3888, 3888] else (if i.val < 94 then [15552, 15552, 15552] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [155520, 155520, 155520])))))))

theorem g32p_row08_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup06_support) :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) c) (g32p_literalTraceValue 7 c)
      [1, -1, 1] (g32p_row08_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row08_tracePolynomial_000
  · exact g32p_row08_tracePolynomial_001
  · exact g32p_row08_tracePolynomial_002
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (18 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_021
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_024
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_028
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_030
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_034
  · exact g32p_row08_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_044
  · exact g32p_row08_tracePolynomial_045
  · exact g32p_row08_tracePolynomial_046
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_075
  · exact g32p_row08_tracePolynomial_076
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_078
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_084
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_087
  · exact g32p_row08_tracePolynomial_088
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_092
  · exact g32p_row08_tracePolynomial_093
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup06_support) hc)
  · exact g32p_row08_tracePolynomial_095
  · exact g32p_row08_tracePolynomial_096
  · exact g32p_row08_tracePolynomial_097
  · exact g32p_row08_tracePolynomial_098
  · exact g32p_row08_tracePolynomial_099
  · exact g32p_row08_tracePolynomial_100
  · exact g32p_row08_tracePolynomial_101

theorem g32p_row08_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 7 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 7 c) := by
  by_cases hc : c ∈ g32p_supplierGroup06_support
  · have hclass (j : Fin 648) :
        IsConj (g32p_literalRepresentative c) (g32p_row08_groupEquiv j : g32p_G) ↔
          g32p_row08_supplierClassifier j = c := by
      simpa only [g32p_row08_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row08_supplierClass_iff (g32p_row08_groupEquiv j) c
    have hχ (j : Fin 648) :
        (g32p_recordedSupplierCharacters 7 (g32p_row08_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row08_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 7 (show (g32p_recordedSuppliers 7).H from g32p_row08_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row08_characterValues (g32p_row08_groupEquiv.symm (g32p_row08_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 7).H (g32p_recordedSupplierCharacters 7)
      (g32p_literalRepresentative c) g32p_row08_groupEquiv g32p_row08_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row08_characterValues j)).val) c 6 648
      (g32p_literalCentralizer c) (g32p_literalTraceValue 7 c) [1, -1, 1]
      (g32p_row08_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row08_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 7)))
      (g32p_row08_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row08_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row08_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
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

theorem g32p_row08_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
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

theorem g32p_row08_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row08_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row08_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 7 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
