import HodgeLean.Foundations.Program.G32PropFourSixPacked0411
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row32_traceSegment_034 (k : ℕ) : List ℤ :=
  if g32p_row32_supplierClassifier (Fin.ofNat 648 k) = 34 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row32_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row32_traceSegment_034_0000_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 0 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0010_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 10 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0000_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 0 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 0 10 10, g32p_row32_traceSegment_034_0000_0010, g32p_row32_traceSegment_034_0010_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0020_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 20 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0030_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 30 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0020_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 20 10 10, g32p_row32_traceSegment_034_0020_0010, g32p_row32_traceSegment_034_0030_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0000_0040 : g32p_coeffSegment g32p_row32_traceSegment_034 0 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 0 20 20, g32p_row32_traceSegment_034_0000_0020, g32p_row32_traceSegment_034_0020_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0040_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 40 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0050_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 50 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0040_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 40 10 10, g32p_row32_traceSegment_034_0040_0010, g32p_row32_traceSegment_034_0050_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0060_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 60 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0070_0011 : g32p_coeffSegment g32p_row32_traceSegment_034 70 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0060_0021 : g32p_coeffSegment g32p_row32_traceSegment_034 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 60 10 11, g32p_row32_traceSegment_034_0060_0010, g32p_row32_traceSegment_034_0070_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0040_0041 : g32p_coeffSegment g32p_row32_traceSegment_034 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 40 20 21, g32p_row32_traceSegment_034_0040_0020, g32p_row32_traceSegment_034_0060_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0000_0081 : g32p_coeffSegment g32p_row32_traceSegment_034 0 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 0 40 41, g32p_row32_traceSegment_034_0000_0040, g32p_row32_traceSegment_034_0040_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0081_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 81 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0091_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 91 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0081_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 81 10 10, g32p_row32_traceSegment_034_0081_0010, g32p_row32_traceSegment_034_0091_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0101_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 101 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0111_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 111 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0101_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 101 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 101 10 10, g32p_row32_traceSegment_034_0101_0010, g32p_row32_traceSegment_034_0111_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0081_0040 : g32p_coeffSegment g32p_row32_traceSegment_034 81 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 81 20 20, g32p_row32_traceSegment_034_0081_0020, g32p_row32_traceSegment_034_0101_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0121_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 121 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0131_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 131 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0121_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 121 20 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 121 10 10, g32p_row32_traceSegment_034_0121_0010, g32p_row32_traceSegment_034_0131_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0141_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 141 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0151_0011 : g32p_coeffSegment g32p_row32_traceSegment_034 151 11 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0141_0021 : g32p_coeffSegment g32p_row32_traceSegment_034 141 21 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 141 10 11, g32p_row32_traceSegment_034_0141_0010, g32p_row32_traceSegment_034_0151_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0121_0041 : g32p_coeffSegment g32p_row32_traceSegment_034 121 41 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 121 20 21, g32p_row32_traceSegment_034_0121_0020, g32p_row32_traceSegment_034_0141_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0081_0081 : g32p_coeffSegment g32p_row32_traceSegment_034 81 81 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 81 40 41, g32p_row32_traceSegment_034_0081_0040, g32p_row32_traceSegment_034_0121_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0000_0162 : g32p_coeffSegment g32p_row32_traceSegment_034 0 162 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 0 81 81, g32p_row32_traceSegment_034_0000_0081, g32p_row32_traceSegment_034_0081_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0162_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 162 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0172_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 172 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0162_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 162 20 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 162 10 10, g32p_row32_traceSegment_034_0162_0010, g32p_row32_traceSegment_034_0172_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0182_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 182 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0192_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 192 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0182_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 182 10 10, g32p_row32_traceSegment_034_0182_0010, g32p_row32_traceSegment_034_0192_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0162_0040 : g32p_coeffSegment g32p_row32_traceSegment_034 162 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 162 20 20, g32p_row32_traceSegment_034_0162_0020, g32p_row32_traceSegment_034_0182_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0202_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 202 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0212_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 212 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0202_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 202 10 10, g32p_row32_traceSegment_034_0202_0010, g32p_row32_traceSegment_034_0212_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0222_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 222 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0232_0011 : g32p_coeffSegment g32p_row32_traceSegment_034 232 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0222_0021 : g32p_coeffSegment g32p_row32_traceSegment_034 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 222 10 11, g32p_row32_traceSegment_034_0222_0010, g32p_row32_traceSegment_034_0232_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0202_0041 : g32p_coeffSegment g32p_row32_traceSegment_034 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 202 20 21, g32p_row32_traceSegment_034_0202_0020, g32p_row32_traceSegment_034_0222_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0162_0081 : g32p_coeffSegment g32p_row32_traceSegment_034 162 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 162 40 41, g32p_row32_traceSegment_034_0162_0040, g32p_row32_traceSegment_034_0202_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0243_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 243 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0253_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 253 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0243_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 243 10 10, g32p_row32_traceSegment_034_0243_0010, g32p_row32_traceSegment_034_0253_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0263_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 263 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0273_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 273 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0263_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 263 10 10, g32p_row32_traceSegment_034_0263_0010, g32p_row32_traceSegment_034_0273_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0243_0040 : g32p_coeffSegment g32p_row32_traceSegment_034 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 243 20 20, g32p_row32_traceSegment_034_0243_0020, g32p_row32_traceSegment_034_0263_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0283_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 283 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0293_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 293 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0283_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 283 10 10, g32p_row32_traceSegment_034_0283_0010, g32p_row32_traceSegment_034_0293_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0303_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 303 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0313_0011 : g32p_coeffSegment g32p_row32_traceSegment_034 313 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0303_0021 : g32p_coeffSegment g32p_row32_traceSegment_034 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 303 10 11, g32p_row32_traceSegment_034_0303_0010, g32p_row32_traceSegment_034_0313_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0283_0041 : g32p_coeffSegment g32p_row32_traceSegment_034 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 283 20 21, g32p_row32_traceSegment_034_0283_0020, g32p_row32_traceSegment_034_0303_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0243_0081 : g32p_coeffSegment g32p_row32_traceSegment_034 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 243 40 41, g32p_row32_traceSegment_034_0243_0040, g32p_row32_traceSegment_034_0283_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0162_0162 : g32p_coeffSegment g32p_row32_traceSegment_034 162 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 162 81 81, g32p_row32_traceSegment_034_0162_0081, g32p_row32_traceSegment_034_0243_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0000_0324 : g32p_coeffSegment g32p_row32_traceSegment_034 0 324 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 0 162 162, g32p_row32_traceSegment_034_0000_0162, g32p_row32_traceSegment_034_0162_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0324_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 324 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0334_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 334 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0324_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 324 10 10, g32p_row32_traceSegment_034_0324_0010, g32p_row32_traceSegment_034_0334_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0344_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 344 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0354_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 354 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0344_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 344 10 10, g32p_row32_traceSegment_034_0344_0010, g32p_row32_traceSegment_034_0354_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0324_0040 : g32p_coeffSegment g32p_row32_traceSegment_034 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 324 20 20, g32p_row32_traceSegment_034_0324_0020, g32p_row32_traceSegment_034_0344_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0364_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 364 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0374_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 374 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0364_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 364 10 10, g32p_row32_traceSegment_034_0364_0010, g32p_row32_traceSegment_034_0374_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0384_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 384 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0394_0011 : g32p_coeffSegment g32p_row32_traceSegment_034 394 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0384_0021 : g32p_coeffSegment g32p_row32_traceSegment_034 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 384 10 11, g32p_row32_traceSegment_034_0384_0010, g32p_row32_traceSegment_034_0394_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0364_0041 : g32p_coeffSegment g32p_row32_traceSegment_034 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 364 20 21, g32p_row32_traceSegment_034_0364_0020, g32p_row32_traceSegment_034_0384_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0324_0081 : g32p_coeffSegment g32p_row32_traceSegment_034 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 324 40 41, g32p_row32_traceSegment_034_0324_0040, g32p_row32_traceSegment_034_0364_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0405_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 405 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0415_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 415 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0405_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 405 10 10, g32p_row32_traceSegment_034_0405_0010, g32p_row32_traceSegment_034_0415_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0425_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 425 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0435_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 435 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0425_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 425 10 10, g32p_row32_traceSegment_034_0425_0010, g32p_row32_traceSegment_034_0435_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0405_0040 : g32p_coeffSegment g32p_row32_traceSegment_034 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 405 20 20, g32p_row32_traceSegment_034_0405_0020, g32p_row32_traceSegment_034_0425_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0445_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 445 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0455_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 455 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0445_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 445 10 10, g32p_row32_traceSegment_034_0445_0010, g32p_row32_traceSegment_034_0455_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0465_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 465 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0475_0011 : g32p_coeffSegment g32p_row32_traceSegment_034 475 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0465_0021 : g32p_coeffSegment g32p_row32_traceSegment_034 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 465 10 11, g32p_row32_traceSegment_034_0465_0010, g32p_row32_traceSegment_034_0475_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0445_0041 : g32p_coeffSegment g32p_row32_traceSegment_034 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 445 20 21, g32p_row32_traceSegment_034_0445_0020, g32p_row32_traceSegment_034_0465_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0405_0081 : g32p_coeffSegment g32p_row32_traceSegment_034 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 405 40 41, g32p_row32_traceSegment_034_0405_0040, g32p_row32_traceSegment_034_0445_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0324_0162 : g32p_coeffSegment g32p_row32_traceSegment_034 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 324 81 81, g32p_row32_traceSegment_034_0324_0081, g32p_row32_traceSegment_034_0405_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0486_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 486 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0496_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 496 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0486_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 486 10 10, g32p_row32_traceSegment_034_0486_0010, g32p_row32_traceSegment_034_0496_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0506_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 506 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0516_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 516 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0506_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 506 20 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 506 10 10, g32p_row32_traceSegment_034_0506_0010, g32p_row32_traceSegment_034_0516_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0486_0040 : g32p_coeffSegment g32p_row32_traceSegment_034 486 40 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 486 20 20, g32p_row32_traceSegment_034_0486_0020, g32p_row32_traceSegment_034_0506_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0526_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 526 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0536_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 536 10 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0526_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 526 20 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 526 10 10, g32p_row32_traceSegment_034_0526_0010, g32p_row32_traceSegment_034_0536_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0546_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 546 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0556_0011 : g32p_coeffSegment g32p_row32_traceSegment_034 556 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0546_0021 : g32p_coeffSegment g32p_row32_traceSegment_034 546 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 546 10 11, g32p_row32_traceSegment_034_0546_0010, g32p_row32_traceSegment_034_0556_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0526_0041 : g32p_coeffSegment g32p_row32_traceSegment_034 526 41 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 526 20 21, g32p_row32_traceSegment_034_0526_0020, g32p_row32_traceSegment_034_0546_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0486_0081 : g32p_coeffSegment g32p_row32_traceSegment_034 486 81 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 486 40 41, g32p_row32_traceSegment_034_0486_0040, g32p_row32_traceSegment_034_0526_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0567_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 567 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0577_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 577 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0567_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 567 10 10, g32p_row32_traceSegment_034_0567_0010, g32p_row32_traceSegment_034_0577_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0587_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 587 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0597_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 597 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0587_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 587 10 10, g32p_row32_traceSegment_034_0587_0010, g32p_row32_traceSegment_034_0597_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0567_0040 : g32p_coeffSegment g32p_row32_traceSegment_034 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 567 20 20, g32p_row32_traceSegment_034_0567_0020, g32p_row32_traceSegment_034_0587_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0607_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 607 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0617_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 617 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0607_0020 : g32p_coeffSegment g32p_row32_traceSegment_034 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 607 10 10, g32p_row32_traceSegment_034_0607_0010, g32p_row32_traceSegment_034_0617_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0627_0010 : g32p_coeffSegment g32p_row32_traceSegment_034 627 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0637_0011 : g32p_coeffSegment g32p_row32_traceSegment_034 637 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_034_0627_0021 : g32p_coeffSegment g32p_row32_traceSegment_034 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 627 10 11, g32p_row32_traceSegment_034_0627_0010, g32p_row32_traceSegment_034_0637_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0607_0041 : g32p_coeffSegment g32p_row32_traceSegment_034 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 607 20 21, g32p_row32_traceSegment_034_0607_0020, g32p_row32_traceSegment_034_0627_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0567_0081 : g32p_coeffSegment g32p_row32_traceSegment_034 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 567 40 41, g32p_row32_traceSegment_034_0567_0040, g32p_row32_traceSegment_034_0607_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0486_0162 : g32p_coeffSegment g32p_row32_traceSegment_034 486 162 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 486 81 81, g32p_row32_traceSegment_034_0486_0081, g32p_row32_traceSegment_034_0567_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0324_0324 : g32p_coeffSegment g32p_row32_traceSegment_034 324 324 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 324 162 162, g32p_row32_traceSegment_034_0324_0162, g32p_row32_traceSegment_034_0486_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_034_0000_0648 : g32p_coeffSegment g32p_row32_traceSegment_034 0 648 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_034 0 324 324, g32p_row32_traceSegment_034_0000_0324, g32p_row32_traceSegment_034_0324_0324]
  decide +kernel

theorem g32p_row32_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 34 = [0, 0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row32_traceSegment_034_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row32_traceSegment_035 (k : ℕ) : List ℤ :=
  if g32p_row32_supplierClassifier (Fin.ofNat 648 k) = 35 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row32_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row32_traceSegment_035_0000_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 0 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0010_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 10 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0000_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 0 10 10, g32p_row32_traceSegment_035_0000_0010, g32p_row32_traceSegment_035_0010_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0020_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 20 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0030_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 30 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0020_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 20 10 10, g32p_row32_traceSegment_035_0020_0010, g32p_row32_traceSegment_035_0030_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0000_0040 : g32p_coeffSegment g32p_row32_traceSegment_035 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 0 20 20, g32p_row32_traceSegment_035_0000_0020, g32p_row32_traceSegment_035_0020_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0040_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 40 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0050_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 50 10 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0040_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 40 20 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 40 10 10, g32p_row32_traceSegment_035_0040_0010, g32p_row32_traceSegment_035_0050_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0060_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 60 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0070_0011 : g32p_coeffSegment g32p_row32_traceSegment_035 70 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0060_0021 : g32p_coeffSegment g32p_row32_traceSegment_035 60 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 60 10 11, g32p_row32_traceSegment_035_0060_0010, g32p_row32_traceSegment_035_0070_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0040_0041 : g32p_coeffSegment g32p_row32_traceSegment_035 40 41 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 40 20 21, g32p_row32_traceSegment_035_0040_0020, g32p_row32_traceSegment_035_0060_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0000_0081 : g32p_coeffSegment g32p_row32_traceSegment_035 0 81 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 0 40 41, g32p_row32_traceSegment_035_0000_0040, g32p_row32_traceSegment_035_0040_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0081_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 81 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0091_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 91 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0081_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 81 10 10, g32p_row32_traceSegment_035_0081_0010, g32p_row32_traceSegment_035_0091_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0101_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 101 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0111_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 111 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0101_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 101 10 10, g32p_row32_traceSegment_035_0101_0010, g32p_row32_traceSegment_035_0111_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0081_0040 : g32p_coeffSegment g32p_row32_traceSegment_035 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 81 20 20, g32p_row32_traceSegment_035_0081_0020, g32p_row32_traceSegment_035_0101_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0121_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 121 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0131_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 131 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0121_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 121 10 10, g32p_row32_traceSegment_035_0121_0010, g32p_row32_traceSegment_035_0131_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0141_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 141 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0151_0011 : g32p_coeffSegment g32p_row32_traceSegment_035 151 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0141_0021 : g32p_coeffSegment g32p_row32_traceSegment_035 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 141 10 11, g32p_row32_traceSegment_035_0141_0010, g32p_row32_traceSegment_035_0151_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0121_0041 : g32p_coeffSegment g32p_row32_traceSegment_035 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 121 20 21, g32p_row32_traceSegment_035_0121_0020, g32p_row32_traceSegment_035_0141_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0081_0081 : g32p_coeffSegment g32p_row32_traceSegment_035 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 81 40 41, g32p_row32_traceSegment_035_0081_0040, g32p_row32_traceSegment_035_0121_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0000_0162 : g32p_coeffSegment g32p_row32_traceSegment_035 0 162 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 0 81 81, g32p_row32_traceSegment_035_0000_0081, g32p_row32_traceSegment_035_0081_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0162_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 162 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0172_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 172 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0162_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 162 10 10, g32p_row32_traceSegment_035_0162_0010, g32p_row32_traceSegment_035_0172_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0182_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 182 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0192_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 192 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0182_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 182 10 10, g32p_row32_traceSegment_035_0182_0010, g32p_row32_traceSegment_035_0192_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0162_0040 : g32p_coeffSegment g32p_row32_traceSegment_035 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 162 20 20, g32p_row32_traceSegment_035_0162_0020, g32p_row32_traceSegment_035_0182_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0202_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 202 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0212_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 212 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0202_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 202 10 10, g32p_row32_traceSegment_035_0202_0010, g32p_row32_traceSegment_035_0212_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0222_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 222 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0232_0011 : g32p_coeffSegment g32p_row32_traceSegment_035 232 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0222_0021 : g32p_coeffSegment g32p_row32_traceSegment_035 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 222 10 11, g32p_row32_traceSegment_035_0222_0010, g32p_row32_traceSegment_035_0232_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0202_0041 : g32p_coeffSegment g32p_row32_traceSegment_035 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 202 20 21, g32p_row32_traceSegment_035_0202_0020, g32p_row32_traceSegment_035_0222_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0162_0081 : g32p_coeffSegment g32p_row32_traceSegment_035 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 162 40 41, g32p_row32_traceSegment_035_0162_0040, g32p_row32_traceSegment_035_0202_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0243_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 243 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0253_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 253 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0243_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 243 10 10, g32p_row32_traceSegment_035_0243_0010, g32p_row32_traceSegment_035_0253_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0263_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 263 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0273_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 273 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0263_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 263 10 10, g32p_row32_traceSegment_035_0263_0010, g32p_row32_traceSegment_035_0273_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0243_0040 : g32p_coeffSegment g32p_row32_traceSegment_035 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 243 20 20, g32p_row32_traceSegment_035_0243_0020, g32p_row32_traceSegment_035_0263_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0283_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 283 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0293_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 293 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0283_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 283 10 10, g32p_row32_traceSegment_035_0283_0010, g32p_row32_traceSegment_035_0293_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0303_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 303 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0313_0011 : g32p_coeffSegment g32p_row32_traceSegment_035 313 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0303_0021 : g32p_coeffSegment g32p_row32_traceSegment_035 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 303 10 11, g32p_row32_traceSegment_035_0303_0010, g32p_row32_traceSegment_035_0313_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0283_0041 : g32p_coeffSegment g32p_row32_traceSegment_035 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 283 20 21, g32p_row32_traceSegment_035_0283_0020, g32p_row32_traceSegment_035_0303_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0243_0081 : g32p_coeffSegment g32p_row32_traceSegment_035 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 243 40 41, g32p_row32_traceSegment_035_0243_0040, g32p_row32_traceSegment_035_0283_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0162_0162 : g32p_coeffSegment g32p_row32_traceSegment_035 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 162 81 81, g32p_row32_traceSegment_035_0162_0081, g32p_row32_traceSegment_035_0243_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0000_0324 : g32p_coeffSegment g32p_row32_traceSegment_035 0 324 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 0 162 162, g32p_row32_traceSegment_035_0000_0162, g32p_row32_traceSegment_035_0162_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0324_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 324 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0334_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 334 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0324_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 324 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 324 10 10, g32p_row32_traceSegment_035_0324_0010, g32p_row32_traceSegment_035_0334_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0344_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 344 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0354_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 354 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0344_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 344 20 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 344 10 10, g32p_row32_traceSegment_035_0344_0010, g32p_row32_traceSegment_035_0354_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0324_0040 : g32p_coeffSegment g32p_row32_traceSegment_035 324 40 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 324 20 20, g32p_row32_traceSegment_035_0324_0020, g32p_row32_traceSegment_035_0344_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0364_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 364 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0374_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 374 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0364_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 364 10 10, g32p_row32_traceSegment_035_0364_0010, g32p_row32_traceSegment_035_0374_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0384_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 384 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0394_0011 : g32p_coeffSegment g32p_row32_traceSegment_035 394 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0384_0021 : g32p_coeffSegment g32p_row32_traceSegment_035 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 384 10 11, g32p_row32_traceSegment_035_0384_0010, g32p_row32_traceSegment_035_0394_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0364_0041 : g32p_coeffSegment g32p_row32_traceSegment_035 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 364 20 21, g32p_row32_traceSegment_035_0364_0020, g32p_row32_traceSegment_035_0384_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0324_0081 : g32p_coeffSegment g32p_row32_traceSegment_035 324 81 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 324 40 41, g32p_row32_traceSegment_035_0324_0040, g32p_row32_traceSegment_035_0364_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0405_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 405 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0415_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 415 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0405_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 405 10 10, g32p_row32_traceSegment_035_0405_0010, g32p_row32_traceSegment_035_0415_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0425_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 425 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0435_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 435 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0425_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 425 10 10, g32p_row32_traceSegment_035_0425_0010, g32p_row32_traceSegment_035_0435_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0405_0040 : g32p_coeffSegment g32p_row32_traceSegment_035 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 405 20 20, g32p_row32_traceSegment_035_0405_0020, g32p_row32_traceSegment_035_0425_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0445_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 445 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0455_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 455 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0445_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 445 10 10, g32p_row32_traceSegment_035_0445_0010, g32p_row32_traceSegment_035_0455_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0465_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 465 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0475_0011 : g32p_coeffSegment g32p_row32_traceSegment_035 475 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0465_0021 : g32p_coeffSegment g32p_row32_traceSegment_035 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 465 10 11, g32p_row32_traceSegment_035_0465_0010, g32p_row32_traceSegment_035_0475_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0445_0041 : g32p_coeffSegment g32p_row32_traceSegment_035 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 445 20 21, g32p_row32_traceSegment_035_0445_0020, g32p_row32_traceSegment_035_0465_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0405_0081 : g32p_coeffSegment g32p_row32_traceSegment_035 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 405 40 41, g32p_row32_traceSegment_035_0405_0040, g32p_row32_traceSegment_035_0445_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0324_0162 : g32p_coeffSegment g32p_row32_traceSegment_035 324 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 324 81 81, g32p_row32_traceSegment_035_0324_0081, g32p_row32_traceSegment_035_0405_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0486_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 486 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0496_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 496 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0486_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 486 10 10, g32p_row32_traceSegment_035_0486_0010, g32p_row32_traceSegment_035_0496_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0506_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 506 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0516_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 516 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0506_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 506 10 10, g32p_row32_traceSegment_035_0506_0010, g32p_row32_traceSegment_035_0516_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0486_0040 : g32p_coeffSegment g32p_row32_traceSegment_035 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 486 20 20, g32p_row32_traceSegment_035_0486_0020, g32p_row32_traceSegment_035_0506_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0526_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 526 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0536_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 536 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0526_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 526 10 10, g32p_row32_traceSegment_035_0526_0010, g32p_row32_traceSegment_035_0536_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0546_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 546 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0556_0011 : g32p_coeffSegment g32p_row32_traceSegment_035 556 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0546_0021 : g32p_coeffSegment g32p_row32_traceSegment_035 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 546 10 11, g32p_row32_traceSegment_035_0546_0010, g32p_row32_traceSegment_035_0556_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0526_0041 : g32p_coeffSegment g32p_row32_traceSegment_035 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 526 20 21, g32p_row32_traceSegment_035_0526_0020, g32p_row32_traceSegment_035_0546_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0486_0081 : g32p_coeffSegment g32p_row32_traceSegment_035 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 486 40 41, g32p_row32_traceSegment_035_0486_0040, g32p_row32_traceSegment_035_0526_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0567_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 567 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0577_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 577 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0567_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 567 10 10, g32p_row32_traceSegment_035_0567_0010, g32p_row32_traceSegment_035_0577_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0587_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 587 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0597_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 597 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0587_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 587 10 10, g32p_row32_traceSegment_035_0587_0010, g32p_row32_traceSegment_035_0597_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0567_0040 : g32p_coeffSegment g32p_row32_traceSegment_035 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 567 20 20, g32p_row32_traceSegment_035_0567_0020, g32p_row32_traceSegment_035_0587_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0607_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 607 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0617_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 617 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0607_0020 : g32p_coeffSegment g32p_row32_traceSegment_035 607 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 607 10 10, g32p_row32_traceSegment_035_0607_0010, g32p_row32_traceSegment_035_0617_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0627_0010 : g32p_coeffSegment g32p_row32_traceSegment_035 627 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0637_0011 : g32p_coeffSegment g32p_row32_traceSegment_035 637 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_035_0627_0021 : g32p_coeffSegment g32p_row32_traceSegment_035 627 21 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 627 10 11, g32p_row32_traceSegment_035_0627_0010, g32p_row32_traceSegment_035_0637_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0607_0041 : g32p_coeffSegment g32p_row32_traceSegment_035 607 41 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 607 20 21, g32p_row32_traceSegment_035_0607_0020, g32p_row32_traceSegment_035_0627_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0567_0081 : g32p_coeffSegment g32p_row32_traceSegment_035 567 81 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 567 40 41, g32p_row32_traceSegment_035_0567_0040, g32p_row32_traceSegment_035_0607_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0486_0162 : g32p_coeffSegment g32p_row32_traceSegment_035 486 162 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 486 81 81, g32p_row32_traceSegment_035_0486_0081, g32p_row32_traceSegment_035_0567_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0324_0324 : g32p_coeffSegment g32p_row32_traceSegment_035 324 324 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 324 162 162, g32p_row32_traceSegment_035_0324_0162, g32p_row32_traceSegment_035_0486_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_035_0000_0648 : g32p_coeffSegment g32p_row32_traceSegment_035 0 648 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_035 0 324 324, g32p_row32_traceSegment_035_0000_0324, g32p_row32_traceSegment_035_0324_0324]
  decide +kernel

theorem g32p_row32_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 35 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row32_traceSegment_035_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row32_traceSegment_037 (k : ℕ) : List ℤ :=
  if g32p_row32_supplierClassifier (Fin.ofNat 648 k) = 37 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row32_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row32_traceSegment_037_0000_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 0 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0010_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 10 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0000_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 0 10 10, g32p_row32_traceSegment_037_0000_0010, g32p_row32_traceSegment_037_0010_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0020_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 20 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0030_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 30 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0020_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 20 10 10, g32p_row32_traceSegment_037_0020_0010, g32p_row32_traceSegment_037_0030_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0000_0040 : g32p_coeffSegment g32p_row32_traceSegment_037 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 0 20 20, g32p_row32_traceSegment_037_0000_0020, g32p_row32_traceSegment_037_0020_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0040_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 40 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0050_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 50 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0040_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 40 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 40 10 10, g32p_row32_traceSegment_037_0040_0010, g32p_row32_traceSegment_037_0050_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0060_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 60 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0070_0011 : g32p_coeffSegment g32p_row32_traceSegment_037 70 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0060_0021 : g32p_coeffSegment g32p_row32_traceSegment_037 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 60 10 11, g32p_row32_traceSegment_037_0060_0010, g32p_row32_traceSegment_037_0070_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0040_0041 : g32p_coeffSegment g32p_row32_traceSegment_037 40 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 40 20 21, g32p_row32_traceSegment_037_0040_0020, g32p_row32_traceSegment_037_0060_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0000_0081 : g32p_coeffSegment g32p_row32_traceSegment_037 0 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 0 40 41, g32p_row32_traceSegment_037_0000_0040, g32p_row32_traceSegment_037_0040_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0081_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 81 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0091_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 91 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0081_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 81 10 10, g32p_row32_traceSegment_037_0081_0010, g32p_row32_traceSegment_037_0091_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0101_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 101 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0111_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 111 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0101_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 101 10 10, g32p_row32_traceSegment_037_0101_0010, g32p_row32_traceSegment_037_0111_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0081_0040 : g32p_coeffSegment g32p_row32_traceSegment_037 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 81 20 20, g32p_row32_traceSegment_037_0081_0020, g32p_row32_traceSegment_037_0101_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0121_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 121 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0131_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 131 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0121_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 121 10 10, g32p_row32_traceSegment_037_0121_0010, g32p_row32_traceSegment_037_0131_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0141_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 141 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0151_0011 : g32p_coeffSegment g32p_row32_traceSegment_037 151 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0141_0021 : g32p_coeffSegment g32p_row32_traceSegment_037 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 141 10 11, g32p_row32_traceSegment_037_0141_0010, g32p_row32_traceSegment_037_0151_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0121_0041 : g32p_coeffSegment g32p_row32_traceSegment_037 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 121 20 21, g32p_row32_traceSegment_037_0121_0020, g32p_row32_traceSegment_037_0141_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0081_0081 : g32p_coeffSegment g32p_row32_traceSegment_037 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 81 40 41, g32p_row32_traceSegment_037_0081_0040, g32p_row32_traceSegment_037_0121_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0000_0162 : g32p_coeffSegment g32p_row32_traceSegment_037 0 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 0 81 81, g32p_row32_traceSegment_037_0000_0081, g32p_row32_traceSegment_037_0081_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0162_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 162 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0172_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 172 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0162_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 162 10 10, g32p_row32_traceSegment_037_0162_0010, g32p_row32_traceSegment_037_0172_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0182_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 182 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0192_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 192 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0182_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 182 10 10, g32p_row32_traceSegment_037_0182_0010, g32p_row32_traceSegment_037_0192_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0162_0040 : g32p_coeffSegment g32p_row32_traceSegment_037 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 162 20 20, g32p_row32_traceSegment_037_0162_0020, g32p_row32_traceSegment_037_0182_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0202_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 202 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0212_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 212 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0202_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 202 10 10, g32p_row32_traceSegment_037_0202_0010, g32p_row32_traceSegment_037_0212_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0222_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 222 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0232_0011 : g32p_coeffSegment g32p_row32_traceSegment_037 232 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0222_0021 : g32p_coeffSegment g32p_row32_traceSegment_037 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 222 10 11, g32p_row32_traceSegment_037_0222_0010, g32p_row32_traceSegment_037_0232_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0202_0041 : g32p_coeffSegment g32p_row32_traceSegment_037 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 202 20 21, g32p_row32_traceSegment_037_0202_0020, g32p_row32_traceSegment_037_0222_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0162_0081 : g32p_coeffSegment g32p_row32_traceSegment_037 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 162 40 41, g32p_row32_traceSegment_037_0162_0040, g32p_row32_traceSegment_037_0202_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0243_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 243 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0253_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 253 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0243_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 243 10 10, g32p_row32_traceSegment_037_0243_0010, g32p_row32_traceSegment_037_0253_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0263_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 263 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0273_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 273 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0263_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 263 10 10, g32p_row32_traceSegment_037_0263_0010, g32p_row32_traceSegment_037_0273_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0243_0040 : g32p_coeffSegment g32p_row32_traceSegment_037 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 243 20 20, g32p_row32_traceSegment_037_0243_0020, g32p_row32_traceSegment_037_0263_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0283_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 283 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0293_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 293 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0283_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 283 10 10, g32p_row32_traceSegment_037_0283_0010, g32p_row32_traceSegment_037_0293_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0303_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 303 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0313_0011 : g32p_coeffSegment g32p_row32_traceSegment_037 313 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0303_0021 : g32p_coeffSegment g32p_row32_traceSegment_037 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 303 10 11, g32p_row32_traceSegment_037_0303_0010, g32p_row32_traceSegment_037_0313_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0283_0041 : g32p_coeffSegment g32p_row32_traceSegment_037 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 283 20 21, g32p_row32_traceSegment_037_0283_0020, g32p_row32_traceSegment_037_0303_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0243_0081 : g32p_coeffSegment g32p_row32_traceSegment_037 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 243 40 41, g32p_row32_traceSegment_037_0243_0040, g32p_row32_traceSegment_037_0283_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0162_0162 : g32p_coeffSegment g32p_row32_traceSegment_037 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 162 81 81, g32p_row32_traceSegment_037_0162_0081, g32p_row32_traceSegment_037_0243_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0000_0324 : g32p_coeffSegment g32p_row32_traceSegment_037 0 324 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 0 162 162, g32p_row32_traceSegment_037_0000_0162, g32p_row32_traceSegment_037_0162_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0324_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 324 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0334_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 334 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0324_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 324 10 10, g32p_row32_traceSegment_037_0324_0010, g32p_row32_traceSegment_037_0334_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0344_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 344 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0354_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 354 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0344_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 344 10 10, g32p_row32_traceSegment_037_0344_0010, g32p_row32_traceSegment_037_0354_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0324_0040 : g32p_coeffSegment g32p_row32_traceSegment_037 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 324 20 20, g32p_row32_traceSegment_037_0324_0020, g32p_row32_traceSegment_037_0344_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0364_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 364 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0374_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 374 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0364_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 364 10 10, g32p_row32_traceSegment_037_0364_0010, g32p_row32_traceSegment_037_0374_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0384_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 384 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0394_0011 : g32p_coeffSegment g32p_row32_traceSegment_037 394 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0384_0021 : g32p_coeffSegment g32p_row32_traceSegment_037 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 384 10 11, g32p_row32_traceSegment_037_0384_0010, g32p_row32_traceSegment_037_0394_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0364_0041 : g32p_coeffSegment g32p_row32_traceSegment_037 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 364 20 21, g32p_row32_traceSegment_037_0364_0020, g32p_row32_traceSegment_037_0384_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0324_0081 : g32p_coeffSegment g32p_row32_traceSegment_037 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 324 40 41, g32p_row32_traceSegment_037_0324_0040, g32p_row32_traceSegment_037_0364_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0405_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 405 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0415_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 415 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0405_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 405 10 10, g32p_row32_traceSegment_037_0405_0010, g32p_row32_traceSegment_037_0415_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0425_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 425 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0435_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 435 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0425_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 425 10 10, g32p_row32_traceSegment_037_0425_0010, g32p_row32_traceSegment_037_0435_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0405_0040 : g32p_coeffSegment g32p_row32_traceSegment_037 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 405 20 20, g32p_row32_traceSegment_037_0405_0020, g32p_row32_traceSegment_037_0425_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0445_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 445 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0455_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 455 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0445_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 445 10 10, g32p_row32_traceSegment_037_0445_0010, g32p_row32_traceSegment_037_0455_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0465_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 465 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0475_0011 : g32p_coeffSegment g32p_row32_traceSegment_037 475 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0465_0021 : g32p_coeffSegment g32p_row32_traceSegment_037 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 465 10 11, g32p_row32_traceSegment_037_0465_0010, g32p_row32_traceSegment_037_0475_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0445_0041 : g32p_coeffSegment g32p_row32_traceSegment_037 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 445 20 21, g32p_row32_traceSegment_037_0445_0020, g32p_row32_traceSegment_037_0465_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0405_0081 : g32p_coeffSegment g32p_row32_traceSegment_037 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 405 40 41, g32p_row32_traceSegment_037_0405_0040, g32p_row32_traceSegment_037_0445_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0324_0162 : g32p_coeffSegment g32p_row32_traceSegment_037 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 324 81 81, g32p_row32_traceSegment_037_0324_0081, g32p_row32_traceSegment_037_0405_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0486_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 486 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0496_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 496 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0486_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 486 10 10, g32p_row32_traceSegment_037_0486_0010, g32p_row32_traceSegment_037_0496_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0506_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 506 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0516_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 516 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0506_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 506 10 10, g32p_row32_traceSegment_037_0506_0010, g32p_row32_traceSegment_037_0516_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0486_0040 : g32p_coeffSegment g32p_row32_traceSegment_037 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 486 20 20, g32p_row32_traceSegment_037_0486_0020, g32p_row32_traceSegment_037_0506_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0526_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 526 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0536_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 536 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0526_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 526 10 10, g32p_row32_traceSegment_037_0526_0010, g32p_row32_traceSegment_037_0536_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0546_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 546 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0556_0011 : g32p_coeffSegment g32p_row32_traceSegment_037 556 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0546_0021 : g32p_coeffSegment g32p_row32_traceSegment_037 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 546 10 11, g32p_row32_traceSegment_037_0546_0010, g32p_row32_traceSegment_037_0556_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0526_0041 : g32p_coeffSegment g32p_row32_traceSegment_037 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 526 20 21, g32p_row32_traceSegment_037_0526_0020, g32p_row32_traceSegment_037_0546_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0486_0081 : g32p_coeffSegment g32p_row32_traceSegment_037 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 486 40 41, g32p_row32_traceSegment_037_0486_0040, g32p_row32_traceSegment_037_0526_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0567_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 567 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0577_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 577 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0567_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 567 10 10, g32p_row32_traceSegment_037_0567_0010, g32p_row32_traceSegment_037_0577_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0587_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 587 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0597_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 597 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0587_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 587 10 10, g32p_row32_traceSegment_037_0587_0010, g32p_row32_traceSegment_037_0597_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0567_0040 : g32p_coeffSegment g32p_row32_traceSegment_037 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 567 20 20, g32p_row32_traceSegment_037_0567_0020, g32p_row32_traceSegment_037_0587_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0607_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 607 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0617_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 617 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0607_0020 : g32p_coeffSegment g32p_row32_traceSegment_037 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 607 10 10, g32p_row32_traceSegment_037_0607_0010, g32p_row32_traceSegment_037_0617_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0627_0010 : g32p_coeffSegment g32p_row32_traceSegment_037 627 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0637_0011 : g32p_coeffSegment g32p_row32_traceSegment_037 637 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_037_0627_0021 : g32p_coeffSegment g32p_row32_traceSegment_037 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 627 10 11, g32p_row32_traceSegment_037_0627_0010, g32p_row32_traceSegment_037_0637_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0607_0041 : g32p_coeffSegment g32p_row32_traceSegment_037 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 607 20 21, g32p_row32_traceSegment_037_0607_0020, g32p_row32_traceSegment_037_0627_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0567_0081 : g32p_coeffSegment g32p_row32_traceSegment_037 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 567 40 41, g32p_row32_traceSegment_037_0567_0040, g32p_row32_traceSegment_037_0607_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0486_0162 : g32p_coeffSegment g32p_row32_traceSegment_037 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 486 81 81, g32p_row32_traceSegment_037_0486_0081, g32p_row32_traceSegment_037_0567_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0324_0324 : g32p_coeffSegment g32p_row32_traceSegment_037 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 324 162 162, g32p_row32_traceSegment_037_0324_0162, g32p_row32_traceSegment_037_0486_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_037_0000_0648 : g32p_coeffSegment g32p_row32_traceSegment_037 0 648 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_037 0 324 324, g32p_row32_traceSegment_037_0000_0324, g32p_row32_traceSegment_037_0324_0324]
  decide +kernel

theorem g32p_row32_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 37 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row32_traceSegment_037_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row32_traceSegment_038 (k : ℕ) : List ℤ :=
  if g32p_row32_supplierClassifier (Fin.ofNat 648 k) = 38 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row32_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row32_traceSegment_038_0000_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 0 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0010_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 10 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0000_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 0 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 0 10 10, g32p_row32_traceSegment_038_0000_0010, g32p_row32_traceSegment_038_0010_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0020_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 20 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0030_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 30 10 = [3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0020_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 20 20 = [3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 20 10 10, g32p_row32_traceSegment_038_0020_0010, g32p_row32_traceSegment_038_0030_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0000_0040 : g32p_coeffSegment g32p_row32_traceSegment_038 0 40 = [5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 0 20 20, g32p_row32_traceSegment_038_0000_0020, g32p_row32_traceSegment_038_0020_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0040_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 40 10 = [5] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0050_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 50 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0040_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 40 20 = [5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 40 10 10, g32p_row32_traceSegment_038_0040_0010, g32p_row32_traceSegment_038_0050_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0060_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 60 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0070_0011 : g32p_coeffSegment g32p_row32_traceSegment_038 70 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0060_0021 : g32p_coeffSegment g32p_row32_traceSegment_038 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 60 10 11, g32p_row32_traceSegment_038_0060_0010, g32p_row32_traceSegment_038_0070_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0040_0041 : g32p_coeffSegment g32p_row32_traceSegment_038 40 41 = [5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 40 20 21, g32p_row32_traceSegment_038_0040_0020, g32p_row32_traceSegment_038_0060_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0000_0081 : g32p_coeffSegment g32p_row32_traceSegment_038 0 81 = [10] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 0 40 41, g32p_row32_traceSegment_038_0000_0040, g32p_row32_traceSegment_038_0040_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0081_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 81 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0091_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 91 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0081_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 81 10 10, g32p_row32_traceSegment_038_0081_0010, g32p_row32_traceSegment_038_0091_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0101_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 101 10 = [5] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0111_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 111 10 = [3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0101_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 101 20 = [8] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 101 10 10, g32p_row32_traceSegment_038_0101_0010, g32p_row32_traceSegment_038_0111_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0081_0040 : g32p_coeffSegment g32p_row32_traceSegment_038 81 40 = [8] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 81 20 20, g32p_row32_traceSegment_038_0081_0020, g32p_row32_traceSegment_038_0101_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0121_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 121 10 = [6] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0131_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 131 10 = [3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0121_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 121 20 = [9] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 121 10 10, g32p_row32_traceSegment_038_0121_0010, g32p_row32_traceSegment_038_0131_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0141_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 141 10 = [7] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0151_0011 : g32p_coeffSegment g32p_row32_traceSegment_038 151 11 = [3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0141_0021 : g32p_coeffSegment g32p_row32_traceSegment_038 141 21 = [10] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 141 10 11, g32p_row32_traceSegment_038_0141_0010, g32p_row32_traceSegment_038_0151_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0121_0041 : g32p_coeffSegment g32p_row32_traceSegment_038 121 41 = [19] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 121 20 21, g32p_row32_traceSegment_038_0121_0020, g32p_row32_traceSegment_038_0141_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0081_0081 : g32p_coeffSegment g32p_row32_traceSegment_038 81 81 = [27] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 81 40 41, g32p_row32_traceSegment_038_0081_0040, g32p_row32_traceSegment_038_0121_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0000_0162 : g32p_coeffSegment g32p_row32_traceSegment_038 0 162 = [37] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 0 81 81, g32p_row32_traceSegment_038_0000_0081, g32p_row32_traceSegment_038_0081_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0162_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 162 10 = [4] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0172_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 172 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0162_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 162 20 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 162 10 10, g32p_row32_traceSegment_038_0162_0010, g32p_row32_traceSegment_038_0172_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0182_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 182 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0192_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 192 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0182_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 182 10 10, g32p_row32_traceSegment_038_0182_0010, g32p_row32_traceSegment_038_0192_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0162_0040 : g32p_coeffSegment g32p_row32_traceSegment_038 162 40 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 162 20 20, g32p_row32_traceSegment_038_0162_0020, g32p_row32_traceSegment_038_0182_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0202_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 202 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0212_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 212 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0202_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 202 10 10, g32p_row32_traceSegment_038_0202_0010, g32p_row32_traceSegment_038_0212_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0222_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 222 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0232_0011 : g32p_coeffSegment g32p_row32_traceSegment_038 232 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0222_0021 : g32p_coeffSegment g32p_row32_traceSegment_038 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 222 10 11, g32p_row32_traceSegment_038_0222_0010, g32p_row32_traceSegment_038_0232_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0202_0041 : g32p_coeffSegment g32p_row32_traceSegment_038 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 202 20 21, g32p_row32_traceSegment_038_0202_0020, g32p_row32_traceSegment_038_0222_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0162_0081 : g32p_coeffSegment g32p_row32_traceSegment_038 162 81 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 162 40 41, g32p_row32_traceSegment_038_0162_0040, g32p_row32_traceSegment_038_0202_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0243_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 243 10 = [2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0253_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 253 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0243_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 243 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 243 10 10, g32p_row32_traceSegment_038_0243_0010, g32p_row32_traceSegment_038_0253_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0263_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 263 10 = [3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0273_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 273 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0263_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 263 20 = [3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 263 10 10, g32p_row32_traceSegment_038_0263_0010, g32p_row32_traceSegment_038_0273_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0243_0040 : g32p_coeffSegment g32p_row32_traceSegment_038 243 40 = [5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 243 20 20, g32p_row32_traceSegment_038_0243_0020, g32p_row32_traceSegment_038_0263_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0283_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 283 10 = [3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0293_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 293 10 = [6] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0283_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 283 20 = [9] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 283 10 10, g32p_row32_traceSegment_038_0283_0010, g32p_row32_traceSegment_038_0293_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0303_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 303 10 = [3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0313_0011 : g32p_coeffSegment g32p_row32_traceSegment_038 313 11 = [7] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0303_0021 : g32p_coeffSegment g32p_row32_traceSegment_038 303 21 = [10] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 303 10 11, g32p_row32_traceSegment_038_0303_0010, g32p_row32_traceSegment_038_0313_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0283_0041 : g32p_coeffSegment g32p_row32_traceSegment_038 283 41 = [19] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 283 20 21, g32p_row32_traceSegment_038_0283_0020, g32p_row32_traceSegment_038_0303_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0243_0081 : g32p_coeffSegment g32p_row32_traceSegment_038 243 81 = [24] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 243 40 41, g32p_row32_traceSegment_038_0243_0040, g32p_row32_traceSegment_038_0283_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0162_0162 : g32p_coeffSegment g32p_row32_traceSegment_038 162 162 = [28] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 162 81 81, g32p_row32_traceSegment_038_0162_0081, g32p_row32_traceSegment_038_0243_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0000_0324 : g32p_coeffSegment g32p_row32_traceSegment_038 0 324 = [65] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 0 162 162, g32p_row32_traceSegment_038_0000_0162, g32p_row32_traceSegment_038_0162_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0324_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 324 10 = [2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0334_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 334 10 = [3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0324_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 324 20 = [5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 324 10 10, g32p_row32_traceSegment_038_0324_0010, g32p_row32_traceSegment_038_0334_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0344_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 344 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0354_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 354 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0344_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 344 10 10, g32p_row32_traceSegment_038_0344_0010, g32p_row32_traceSegment_038_0354_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0324_0040 : g32p_coeffSegment g32p_row32_traceSegment_038 324 40 = [5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 324 20 20, g32p_row32_traceSegment_038_0324_0020, g32p_row32_traceSegment_038_0344_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0364_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 364 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0374_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 374 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0364_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 364 10 10, g32p_row32_traceSegment_038_0364_0010, g32p_row32_traceSegment_038_0374_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0384_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 384 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0394_0011 : g32p_coeffSegment g32p_row32_traceSegment_038 394 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0384_0021 : g32p_coeffSegment g32p_row32_traceSegment_038 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 384 10 11, g32p_row32_traceSegment_038_0384_0010, g32p_row32_traceSegment_038_0394_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0364_0041 : g32p_coeffSegment g32p_row32_traceSegment_038 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 364 20 21, g32p_row32_traceSegment_038_0364_0020, g32p_row32_traceSegment_038_0384_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0324_0081 : g32p_coeffSegment g32p_row32_traceSegment_038 324 81 = [5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 324 40 41, g32p_row32_traceSegment_038_0324_0040, g32p_row32_traceSegment_038_0364_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0405_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 405 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0415_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 415 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0405_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 405 10 10, g32p_row32_traceSegment_038_0405_0010, g32p_row32_traceSegment_038_0415_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0425_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 425 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0435_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 435 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0425_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 425 10 10, g32p_row32_traceSegment_038_0425_0010, g32p_row32_traceSegment_038_0435_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0405_0040 : g32p_coeffSegment g32p_row32_traceSegment_038 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 405 20 20, g32p_row32_traceSegment_038_0405_0020, g32p_row32_traceSegment_038_0425_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0445_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 445 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0455_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 455 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0445_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 445 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 445 10 10, g32p_row32_traceSegment_038_0445_0010, g32p_row32_traceSegment_038_0455_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0465_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 465 10 = [3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0475_0011 : g32p_coeffSegment g32p_row32_traceSegment_038 475 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0465_0021 : g32p_coeffSegment g32p_row32_traceSegment_038 465 21 = [3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 465 10 11, g32p_row32_traceSegment_038_0465_0010, g32p_row32_traceSegment_038_0475_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0445_0041 : g32p_coeffSegment g32p_row32_traceSegment_038 445 41 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 445 20 21, g32p_row32_traceSegment_038_0445_0020, g32p_row32_traceSegment_038_0465_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0405_0081 : g32p_coeffSegment g32p_row32_traceSegment_038 405 81 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 405 40 41, g32p_row32_traceSegment_038_0405_0040, g32p_row32_traceSegment_038_0445_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0324_0162 : g32p_coeffSegment g32p_row32_traceSegment_038 324 162 = [9] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 324 81 81, g32p_row32_traceSegment_038_0324_0081, g32p_row32_traceSegment_038_0405_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0486_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 486 10 = [2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0496_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 496 10 = [4] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0486_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 486 20 = [6] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 486 10 10, g32p_row32_traceSegment_038_0486_0010, g32p_row32_traceSegment_038_0496_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0506_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 506 10 = [4] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0516_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 516 10 = [6] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0506_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 506 20 = [10] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 506 10 10, g32p_row32_traceSegment_038_0506_0010, g32p_row32_traceSegment_038_0516_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0486_0040 : g32p_coeffSegment g32p_row32_traceSegment_038 486 40 = [16] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 486 20 20, g32p_row32_traceSegment_038_0486_0020, g32p_row32_traceSegment_038_0506_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0526_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 526 10 = [2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0536_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 536 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0526_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 526 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 526 10 10, g32p_row32_traceSegment_038_0526_0010, g32p_row32_traceSegment_038_0536_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0546_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 546 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0556_0011 : g32p_coeffSegment g32p_row32_traceSegment_038 556 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0546_0021 : g32p_coeffSegment g32p_row32_traceSegment_038 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 546 10 11, g32p_row32_traceSegment_038_0546_0010, g32p_row32_traceSegment_038_0556_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0526_0041 : g32p_coeffSegment g32p_row32_traceSegment_038 526 41 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 526 20 21, g32p_row32_traceSegment_038_0526_0020, g32p_row32_traceSegment_038_0546_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0486_0081 : g32p_coeffSegment g32p_row32_traceSegment_038 486 81 = [18] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 486 40 41, g32p_row32_traceSegment_038_0486_0040, g32p_row32_traceSegment_038_0526_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0567_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 567 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0577_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 577 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0567_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 567 10 10, g32p_row32_traceSegment_038_0567_0010, g32p_row32_traceSegment_038_0577_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0587_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 587 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0597_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 597 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0587_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 587 10 10, g32p_row32_traceSegment_038_0587_0010, g32p_row32_traceSegment_038_0597_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0567_0040 : g32p_coeffSegment g32p_row32_traceSegment_038 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 567 20 20, g32p_row32_traceSegment_038_0567_0020, g32p_row32_traceSegment_038_0587_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0607_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 607 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0617_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 617 10 = [8] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0607_0020 : g32p_coeffSegment g32p_row32_traceSegment_038 607 20 = [8] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 607 10 10, g32p_row32_traceSegment_038_0607_0010, g32p_row32_traceSegment_038_0617_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0627_0010 : g32p_coeffSegment g32p_row32_traceSegment_038 627 10 = [7] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0637_0011 : g32p_coeffSegment g32p_row32_traceSegment_038 637 11 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_038_0627_0021 : g32p_coeffSegment g32p_row32_traceSegment_038 627 21 = [8] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 627 10 11, g32p_row32_traceSegment_038_0627_0010, g32p_row32_traceSegment_038_0637_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0607_0041 : g32p_coeffSegment g32p_row32_traceSegment_038 607 41 = [16] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 607 20 21, g32p_row32_traceSegment_038_0607_0020, g32p_row32_traceSegment_038_0627_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0567_0081 : g32p_coeffSegment g32p_row32_traceSegment_038 567 81 = [16] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 567 40 41, g32p_row32_traceSegment_038_0567_0040, g32p_row32_traceSegment_038_0607_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0486_0162 : g32p_coeffSegment g32p_row32_traceSegment_038 486 162 = [34] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 486 81 81, g32p_row32_traceSegment_038_0486_0081, g32p_row32_traceSegment_038_0567_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0324_0324 : g32p_coeffSegment g32p_row32_traceSegment_038 324 324 = [43] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 324 162 162, g32p_row32_traceSegment_038_0324_0162, g32p_row32_traceSegment_038_0486_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_038_0000_0648 : g32p_coeffSegment g32p_row32_traceSegment_038 0 648 = [108] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_038 0 324 324, g32p_row32_traceSegment_038_0000_0324, g32p_row32_traceSegment_038_0324_0324]
  decide +kernel

theorem g32p_row32_traceCoefficients_038 :
    g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 38 = [108] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row32_traceSegment_038_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row32_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 24) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 24) (g32p_literalTraceValue 31 24)
      [1, 1, 1] [] = true := by
  rw [g32p_row32_traceCoefficients_024]
  decide +kernel

theorem g32p_row32_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 28) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 28) (g32p_literalTraceValue 31 28)
      [1, 1, 1] [] = true := by
  rw [g32p_row32_traceCoefficients_028]
  decide +kernel

theorem g32p_row32_tracePolynomial_030 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 30) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 30) (g32p_literalTraceValue 31 30)
      [1, 1, 1] [1296] = true := by
  rw [g32p_row32_traceCoefficients_030]
  decide +kernel

theorem g32p_row32_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 32) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 32) (g32p_literalTraceValue 31 32)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row32_traceCoefficients_032]
  decide +kernel

theorem g32p_row32_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 34) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 34) (g32p_literalTraceValue 31 34)
      [1, 1, 1] [5184] = true := by
  rw [g32p_row32_traceCoefficients_034]
  decide +kernel

theorem g32p_row32_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 35) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 35) (g32p_literalTraceValue 31 35)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row32_traceCoefficients_035]
  decide +kernel

theorem g32p_row32_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 37) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 37) (g32p_literalTraceValue 31 37)
      [1, 1, 1] [155520] = true := by
  rw [g32p_row32_traceCoefficients_037]
  decide +kernel

theorem g32p_row32_tracePolynomial_038 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 38) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 38) (g32p_literalTraceValue 31 38)
      [1, 1, 1] [] = true := by
  rw [g32p_row32_traceCoefficients_038]
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

private def g32p_row32_traceSegment_044 (k : ℕ) : List ℤ :=
  if g32p_row32_supplierClassifier (Fin.ofNat 648 k) = 44 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row32_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row32_traceSegment_044_0000_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 0 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0010_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 10 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0000_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 0 10 10, g32p_row32_traceSegment_044_0000_0010, g32p_row32_traceSegment_044_0010_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0020_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 20 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0030_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 30 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0020_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 20 10 10, g32p_row32_traceSegment_044_0020_0010, g32p_row32_traceSegment_044_0030_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0000_0040 : g32p_coeffSegment g32p_row32_traceSegment_044 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 0 20 20, g32p_row32_traceSegment_044_0000_0020, g32p_row32_traceSegment_044_0020_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0040_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 40 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0050_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 50 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0040_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 40 10 10, g32p_row32_traceSegment_044_0040_0010, g32p_row32_traceSegment_044_0050_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0060_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 60 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0070_0011 : g32p_coeffSegment g32p_row32_traceSegment_044 70 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0060_0021 : g32p_coeffSegment g32p_row32_traceSegment_044 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 60 10 11, g32p_row32_traceSegment_044_0060_0010, g32p_row32_traceSegment_044_0070_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0040_0041 : g32p_coeffSegment g32p_row32_traceSegment_044 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 40 20 21, g32p_row32_traceSegment_044_0040_0020, g32p_row32_traceSegment_044_0060_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0000_0081 : g32p_coeffSegment g32p_row32_traceSegment_044 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 0 40 41, g32p_row32_traceSegment_044_0000_0040, g32p_row32_traceSegment_044_0040_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0081_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 81 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0091_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 91 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0081_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 81 10 10, g32p_row32_traceSegment_044_0081_0010, g32p_row32_traceSegment_044_0091_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0101_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 101 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0111_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 111 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0101_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 101 10 10, g32p_row32_traceSegment_044_0101_0010, g32p_row32_traceSegment_044_0111_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0081_0040 : g32p_coeffSegment g32p_row32_traceSegment_044 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 81 20 20, g32p_row32_traceSegment_044_0081_0020, g32p_row32_traceSegment_044_0101_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0121_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 121 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0131_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 131 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0121_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 121 10 10, g32p_row32_traceSegment_044_0121_0010, g32p_row32_traceSegment_044_0131_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0141_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 141 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0151_0011 : g32p_coeffSegment g32p_row32_traceSegment_044 151 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0141_0021 : g32p_coeffSegment g32p_row32_traceSegment_044 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 141 10 11, g32p_row32_traceSegment_044_0141_0010, g32p_row32_traceSegment_044_0151_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0121_0041 : g32p_coeffSegment g32p_row32_traceSegment_044 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 121 20 21, g32p_row32_traceSegment_044_0121_0020, g32p_row32_traceSegment_044_0141_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0081_0081 : g32p_coeffSegment g32p_row32_traceSegment_044 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 81 40 41, g32p_row32_traceSegment_044_0081_0040, g32p_row32_traceSegment_044_0121_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0000_0162 : g32p_coeffSegment g32p_row32_traceSegment_044 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 0 81 81, g32p_row32_traceSegment_044_0000_0081, g32p_row32_traceSegment_044_0081_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0162_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 162 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0172_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 172 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0162_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 162 10 10, g32p_row32_traceSegment_044_0162_0010, g32p_row32_traceSegment_044_0172_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0182_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 182 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0192_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 192 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0182_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 182 10 10, g32p_row32_traceSegment_044_0182_0010, g32p_row32_traceSegment_044_0192_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0162_0040 : g32p_coeffSegment g32p_row32_traceSegment_044 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 162 20 20, g32p_row32_traceSegment_044_0162_0020, g32p_row32_traceSegment_044_0182_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0202_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 202 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0212_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 212 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0202_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 202 10 10, g32p_row32_traceSegment_044_0202_0010, g32p_row32_traceSegment_044_0212_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0222_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 222 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0232_0011 : g32p_coeffSegment g32p_row32_traceSegment_044 232 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0222_0021 : g32p_coeffSegment g32p_row32_traceSegment_044 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 222 10 11, g32p_row32_traceSegment_044_0222_0010, g32p_row32_traceSegment_044_0232_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0202_0041 : g32p_coeffSegment g32p_row32_traceSegment_044 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 202 20 21, g32p_row32_traceSegment_044_0202_0020, g32p_row32_traceSegment_044_0222_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0162_0081 : g32p_coeffSegment g32p_row32_traceSegment_044 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 162 40 41, g32p_row32_traceSegment_044_0162_0040, g32p_row32_traceSegment_044_0202_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0243_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 243 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0253_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 253 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0243_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 243 10 10, g32p_row32_traceSegment_044_0243_0010, g32p_row32_traceSegment_044_0253_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0263_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 263 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0273_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 273 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0263_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 263 10 10, g32p_row32_traceSegment_044_0263_0010, g32p_row32_traceSegment_044_0273_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0243_0040 : g32p_coeffSegment g32p_row32_traceSegment_044 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 243 20 20, g32p_row32_traceSegment_044_0243_0020, g32p_row32_traceSegment_044_0263_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0283_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 283 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0293_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 293 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0283_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 283 10 10, g32p_row32_traceSegment_044_0283_0010, g32p_row32_traceSegment_044_0293_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0303_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 303 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0313_0011 : g32p_coeffSegment g32p_row32_traceSegment_044 313 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0303_0021 : g32p_coeffSegment g32p_row32_traceSegment_044 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 303 10 11, g32p_row32_traceSegment_044_0303_0010, g32p_row32_traceSegment_044_0313_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0283_0041 : g32p_coeffSegment g32p_row32_traceSegment_044 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 283 20 21, g32p_row32_traceSegment_044_0283_0020, g32p_row32_traceSegment_044_0303_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0243_0081 : g32p_coeffSegment g32p_row32_traceSegment_044 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 243 40 41, g32p_row32_traceSegment_044_0243_0040, g32p_row32_traceSegment_044_0283_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0162_0162 : g32p_coeffSegment g32p_row32_traceSegment_044 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 162 81 81, g32p_row32_traceSegment_044_0162_0081, g32p_row32_traceSegment_044_0243_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0000_0324 : g32p_coeffSegment g32p_row32_traceSegment_044 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 0 162 162, g32p_row32_traceSegment_044_0000_0162, g32p_row32_traceSegment_044_0162_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0324_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 324 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0334_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 334 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0324_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 324 10 10, g32p_row32_traceSegment_044_0324_0010, g32p_row32_traceSegment_044_0334_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0344_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 344 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0354_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 354 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0344_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 344 10 10, g32p_row32_traceSegment_044_0344_0010, g32p_row32_traceSegment_044_0354_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0324_0040 : g32p_coeffSegment g32p_row32_traceSegment_044 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 324 20 20, g32p_row32_traceSegment_044_0324_0020, g32p_row32_traceSegment_044_0344_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0364_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 364 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0374_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 374 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0364_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 364 10 10, g32p_row32_traceSegment_044_0364_0010, g32p_row32_traceSegment_044_0374_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0384_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 384 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0394_0011 : g32p_coeffSegment g32p_row32_traceSegment_044 394 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0384_0021 : g32p_coeffSegment g32p_row32_traceSegment_044 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 384 10 11, g32p_row32_traceSegment_044_0384_0010, g32p_row32_traceSegment_044_0394_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0364_0041 : g32p_coeffSegment g32p_row32_traceSegment_044 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 364 20 21, g32p_row32_traceSegment_044_0364_0020, g32p_row32_traceSegment_044_0384_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0324_0081 : g32p_coeffSegment g32p_row32_traceSegment_044 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 324 40 41, g32p_row32_traceSegment_044_0324_0040, g32p_row32_traceSegment_044_0364_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0405_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 405 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0415_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 415 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0405_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 405 10 10, g32p_row32_traceSegment_044_0405_0010, g32p_row32_traceSegment_044_0415_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0425_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 425 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0435_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 435 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0425_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 425 10 10, g32p_row32_traceSegment_044_0425_0010, g32p_row32_traceSegment_044_0435_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0405_0040 : g32p_coeffSegment g32p_row32_traceSegment_044 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 405 20 20, g32p_row32_traceSegment_044_0405_0020, g32p_row32_traceSegment_044_0425_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0445_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 445 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0455_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 455 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0445_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 445 10 10, g32p_row32_traceSegment_044_0445_0010, g32p_row32_traceSegment_044_0455_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0465_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 465 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0475_0011 : g32p_coeffSegment g32p_row32_traceSegment_044 475 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0465_0021 : g32p_coeffSegment g32p_row32_traceSegment_044 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 465 10 11, g32p_row32_traceSegment_044_0465_0010, g32p_row32_traceSegment_044_0475_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0445_0041 : g32p_coeffSegment g32p_row32_traceSegment_044 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 445 20 21, g32p_row32_traceSegment_044_0445_0020, g32p_row32_traceSegment_044_0465_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0405_0081 : g32p_coeffSegment g32p_row32_traceSegment_044 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 405 40 41, g32p_row32_traceSegment_044_0405_0040, g32p_row32_traceSegment_044_0445_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0324_0162 : g32p_coeffSegment g32p_row32_traceSegment_044 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 324 81 81, g32p_row32_traceSegment_044_0324_0081, g32p_row32_traceSegment_044_0405_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0486_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 486 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0496_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 496 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0486_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 486 10 10, g32p_row32_traceSegment_044_0486_0010, g32p_row32_traceSegment_044_0496_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0506_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 506 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0516_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 516 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0506_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 506 10 10, g32p_row32_traceSegment_044_0506_0010, g32p_row32_traceSegment_044_0516_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0486_0040 : g32p_coeffSegment g32p_row32_traceSegment_044 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 486 20 20, g32p_row32_traceSegment_044_0486_0020, g32p_row32_traceSegment_044_0506_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0526_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 526 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0536_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 536 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0526_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 526 10 10, g32p_row32_traceSegment_044_0526_0010, g32p_row32_traceSegment_044_0536_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0546_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 546 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0556_0011 : g32p_coeffSegment g32p_row32_traceSegment_044 556 11 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0546_0021 : g32p_coeffSegment g32p_row32_traceSegment_044 546 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 546 10 11, g32p_row32_traceSegment_044_0546_0010, g32p_row32_traceSegment_044_0556_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0526_0041 : g32p_coeffSegment g32p_row32_traceSegment_044 526 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 526 20 21, g32p_row32_traceSegment_044_0526_0020, g32p_row32_traceSegment_044_0546_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0486_0081 : g32p_coeffSegment g32p_row32_traceSegment_044 486 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 486 40 41, g32p_row32_traceSegment_044_0486_0040, g32p_row32_traceSegment_044_0526_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0567_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 567 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0577_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 577 10 = [2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0567_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 567 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 567 10 10, g32p_row32_traceSegment_044_0567_0010, g32p_row32_traceSegment_044_0577_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0587_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 587 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0597_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 597 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0587_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 587 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 587 10 10, g32p_row32_traceSegment_044_0587_0010, g32p_row32_traceSegment_044_0597_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0567_0040 : g32p_coeffSegment g32p_row32_traceSegment_044 567 40 = [3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 567 20 20, g32p_row32_traceSegment_044_0567_0020, g32p_row32_traceSegment_044_0587_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0607_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 607 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0617_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 617 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0607_0020 : g32p_coeffSegment g32p_row32_traceSegment_044 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 607 10 10, g32p_row32_traceSegment_044_0607_0010, g32p_row32_traceSegment_044_0617_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0627_0010 : g32p_coeffSegment g32p_row32_traceSegment_044 627 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0637_0011 : g32p_coeffSegment g32p_row32_traceSegment_044 637 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_044_0627_0021 : g32p_coeffSegment g32p_row32_traceSegment_044 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 627 10 11, g32p_row32_traceSegment_044_0627_0010, g32p_row32_traceSegment_044_0637_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0607_0041 : g32p_coeffSegment g32p_row32_traceSegment_044 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 607 20 21, g32p_row32_traceSegment_044_0607_0020, g32p_row32_traceSegment_044_0627_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0567_0081 : g32p_coeffSegment g32p_row32_traceSegment_044 567 81 = [3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 567 40 41, g32p_row32_traceSegment_044_0567_0040, g32p_row32_traceSegment_044_0607_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0486_0162 : g32p_coeffSegment g32p_row32_traceSegment_044 486 162 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 486 81 81, g32p_row32_traceSegment_044_0486_0081, g32p_row32_traceSegment_044_0567_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0324_0324 : g32p_coeffSegment g32p_row32_traceSegment_044 324 324 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 324 162 162, g32p_row32_traceSegment_044_0324_0162, g32p_row32_traceSegment_044_0486_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_044_0000_0648 : g32p_coeffSegment g32p_row32_traceSegment_044 0 648 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_044 0 324 324, g32p_row32_traceSegment_044_0000_0324, g32p_row32_traceSegment_044_0324_0324]
  decide +kernel

theorem g32p_row32_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 44 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row32_traceSegment_044_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row32_traceSegment_045 (k : ℕ) : List ℤ :=
  if g32p_row32_supplierClassifier (Fin.ofNat 648 k) = 45 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row32_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row32_traceSegment_045_0000_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 0 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0010_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 10 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0000_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 0 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 0 10 10, g32p_row32_traceSegment_045_0000_0010, g32p_row32_traceSegment_045_0010_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0020_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 20 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0030_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 30 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0020_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 20 10 10, g32p_row32_traceSegment_045_0020_0010, g32p_row32_traceSegment_045_0030_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0000_0040 : g32p_coeffSegment g32p_row32_traceSegment_045 0 40 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 0 20 20, g32p_row32_traceSegment_045_0000_0020, g32p_row32_traceSegment_045_0020_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0040_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 40 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0050_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 50 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0040_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 40 10 10, g32p_row32_traceSegment_045_0040_0010, g32p_row32_traceSegment_045_0050_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0060_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 60 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0070_0011 : g32p_coeffSegment g32p_row32_traceSegment_045 70 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0060_0021 : g32p_coeffSegment g32p_row32_traceSegment_045 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 60 10 11, g32p_row32_traceSegment_045_0060_0010, g32p_row32_traceSegment_045_0070_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0040_0041 : g32p_coeffSegment g32p_row32_traceSegment_045 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 40 20 21, g32p_row32_traceSegment_045_0040_0020, g32p_row32_traceSegment_045_0060_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0000_0081 : g32p_coeffSegment g32p_row32_traceSegment_045 0 81 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 0 40 41, g32p_row32_traceSegment_045_0000_0040, g32p_row32_traceSegment_045_0040_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0081_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 81 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0091_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 91 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0081_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 81 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 81 10 10, g32p_row32_traceSegment_045_0081_0010, g32p_row32_traceSegment_045_0091_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0101_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 101 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0111_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 111 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0101_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 101 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 101 10 10, g32p_row32_traceSegment_045_0101_0010, g32p_row32_traceSegment_045_0111_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0081_0040 : g32p_coeffSegment g32p_row32_traceSegment_045 81 40 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 81 20 20, g32p_row32_traceSegment_045_0081_0020, g32p_row32_traceSegment_045_0101_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0121_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 121 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0131_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 131 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0121_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 121 10 10, g32p_row32_traceSegment_045_0121_0010, g32p_row32_traceSegment_045_0131_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0141_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 141 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0151_0011 : g32p_coeffSegment g32p_row32_traceSegment_045 151 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0141_0021 : g32p_coeffSegment g32p_row32_traceSegment_045 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 141 10 11, g32p_row32_traceSegment_045_0141_0010, g32p_row32_traceSegment_045_0151_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0121_0041 : g32p_coeffSegment g32p_row32_traceSegment_045 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 121 20 21, g32p_row32_traceSegment_045_0121_0020, g32p_row32_traceSegment_045_0141_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0081_0081 : g32p_coeffSegment g32p_row32_traceSegment_045 81 81 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 81 40 41, g32p_row32_traceSegment_045_0081_0040, g32p_row32_traceSegment_045_0121_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0000_0162 : g32p_coeffSegment g32p_row32_traceSegment_045 0 162 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 0 81 81, g32p_row32_traceSegment_045_0000_0081, g32p_row32_traceSegment_045_0081_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0162_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 162 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0172_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 172 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0162_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 162 10 10, g32p_row32_traceSegment_045_0162_0010, g32p_row32_traceSegment_045_0172_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0182_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 182 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0192_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 192 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0182_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 182 10 10, g32p_row32_traceSegment_045_0182_0010, g32p_row32_traceSegment_045_0192_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0162_0040 : g32p_coeffSegment g32p_row32_traceSegment_045 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 162 20 20, g32p_row32_traceSegment_045_0162_0020, g32p_row32_traceSegment_045_0182_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0202_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 202 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0212_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 212 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0202_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 202 10 10, g32p_row32_traceSegment_045_0202_0010, g32p_row32_traceSegment_045_0212_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0222_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 222 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0232_0011 : g32p_coeffSegment g32p_row32_traceSegment_045 232 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0222_0021 : g32p_coeffSegment g32p_row32_traceSegment_045 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 222 10 11, g32p_row32_traceSegment_045_0222_0010, g32p_row32_traceSegment_045_0232_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0202_0041 : g32p_coeffSegment g32p_row32_traceSegment_045 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 202 20 21, g32p_row32_traceSegment_045_0202_0020, g32p_row32_traceSegment_045_0222_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0162_0081 : g32p_coeffSegment g32p_row32_traceSegment_045 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 162 40 41, g32p_row32_traceSegment_045_0162_0040, g32p_row32_traceSegment_045_0202_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0243_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 243 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0253_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 253 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0243_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 243 10 10, g32p_row32_traceSegment_045_0243_0010, g32p_row32_traceSegment_045_0253_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0263_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 263 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0273_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 273 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0263_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 263 10 10, g32p_row32_traceSegment_045_0263_0010, g32p_row32_traceSegment_045_0273_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0243_0040 : g32p_coeffSegment g32p_row32_traceSegment_045 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 243 20 20, g32p_row32_traceSegment_045_0243_0020, g32p_row32_traceSegment_045_0263_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0283_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 283 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0293_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 293 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0283_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 283 10 10, g32p_row32_traceSegment_045_0283_0010, g32p_row32_traceSegment_045_0293_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0303_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 303 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0313_0011 : g32p_coeffSegment g32p_row32_traceSegment_045 313 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0303_0021 : g32p_coeffSegment g32p_row32_traceSegment_045 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 303 10 11, g32p_row32_traceSegment_045_0303_0010, g32p_row32_traceSegment_045_0313_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0283_0041 : g32p_coeffSegment g32p_row32_traceSegment_045 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 283 20 21, g32p_row32_traceSegment_045_0283_0020, g32p_row32_traceSegment_045_0303_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0243_0081 : g32p_coeffSegment g32p_row32_traceSegment_045 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 243 40 41, g32p_row32_traceSegment_045_0243_0040, g32p_row32_traceSegment_045_0283_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0162_0162 : g32p_coeffSegment g32p_row32_traceSegment_045 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 162 81 81, g32p_row32_traceSegment_045_0162_0081, g32p_row32_traceSegment_045_0243_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0000_0324 : g32p_coeffSegment g32p_row32_traceSegment_045 0 324 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 0 162 162, g32p_row32_traceSegment_045_0000_0162, g32p_row32_traceSegment_045_0162_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0324_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 324 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0334_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 334 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0324_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 324 10 10, g32p_row32_traceSegment_045_0324_0010, g32p_row32_traceSegment_045_0334_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0344_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 344 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0354_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 354 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0344_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 344 10 10, g32p_row32_traceSegment_045_0344_0010, g32p_row32_traceSegment_045_0354_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0324_0040 : g32p_coeffSegment g32p_row32_traceSegment_045 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 324 20 20, g32p_row32_traceSegment_045_0324_0020, g32p_row32_traceSegment_045_0344_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0364_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 364 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0374_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 374 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0364_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 364 10 10, g32p_row32_traceSegment_045_0364_0010, g32p_row32_traceSegment_045_0374_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0384_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 384 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0394_0011 : g32p_coeffSegment g32p_row32_traceSegment_045 394 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0384_0021 : g32p_coeffSegment g32p_row32_traceSegment_045 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 384 10 11, g32p_row32_traceSegment_045_0384_0010, g32p_row32_traceSegment_045_0394_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0364_0041 : g32p_coeffSegment g32p_row32_traceSegment_045 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 364 20 21, g32p_row32_traceSegment_045_0364_0020, g32p_row32_traceSegment_045_0384_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0324_0081 : g32p_coeffSegment g32p_row32_traceSegment_045 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 324 40 41, g32p_row32_traceSegment_045_0324_0040, g32p_row32_traceSegment_045_0364_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0405_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 405 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0415_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 415 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0405_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 405 10 10, g32p_row32_traceSegment_045_0405_0010, g32p_row32_traceSegment_045_0415_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0425_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 425 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0435_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 435 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0425_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 425 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 425 10 10, g32p_row32_traceSegment_045_0425_0010, g32p_row32_traceSegment_045_0435_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0405_0040 : g32p_coeffSegment g32p_row32_traceSegment_045 405 40 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 405 20 20, g32p_row32_traceSegment_045_0405_0020, g32p_row32_traceSegment_045_0425_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0445_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 445 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0455_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 455 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0445_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 445 20 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 445 10 10, g32p_row32_traceSegment_045_0445_0010, g32p_row32_traceSegment_045_0455_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0465_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 465 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0475_0011 : g32p_coeffSegment g32p_row32_traceSegment_045 475 11 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0465_0021 : g32p_coeffSegment g32p_row32_traceSegment_045 465 21 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 465 10 11, g32p_row32_traceSegment_045_0465_0010, g32p_row32_traceSegment_045_0475_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0445_0041 : g32p_coeffSegment g32p_row32_traceSegment_045 445 41 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 445 20 21, g32p_row32_traceSegment_045_0445_0020, g32p_row32_traceSegment_045_0465_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0405_0081 : g32p_coeffSegment g32p_row32_traceSegment_045 405 81 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 405 40 41, g32p_row32_traceSegment_045_0405_0040, g32p_row32_traceSegment_045_0445_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0324_0162 : g32p_coeffSegment g32p_row32_traceSegment_045 324 162 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 324 81 81, g32p_row32_traceSegment_045_0324_0081, g32p_row32_traceSegment_045_0405_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0486_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 486 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0496_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 496 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0486_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 486 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 486 10 10, g32p_row32_traceSegment_045_0486_0010, g32p_row32_traceSegment_045_0496_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0506_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 506 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0516_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 516 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0506_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 506 10 10, g32p_row32_traceSegment_045_0506_0010, g32p_row32_traceSegment_045_0516_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0486_0040 : g32p_coeffSegment g32p_row32_traceSegment_045 486 40 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 486 20 20, g32p_row32_traceSegment_045_0486_0020, g32p_row32_traceSegment_045_0506_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0526_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 526 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0536_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 536 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0526_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 526 10 10, g32p_row32_traceSegment_045_0526_0010, g32p_row32_traceSegment_045_0536_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0546_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 546 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0556_0011 : g32p_coeffSegment g32p_row32_traceSegment_045 556 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0546_0021 : g32p_coeffSegment g32p_row32_traceSegment_045 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 546 10 11, g32p_row32_traceSegment_045_0546_0010, g32p_row32_traceSegment_045_0556_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0526_0041 : g32p_coeffSegment g32p_row32_traceSegment_045 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 526 20 21, g32p_row32_traceSegment_045_0526_0020, g32p_row32_traceSegment_045_0546_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0486_0081 : g32p_coeffSegment g32p_row32_traceSegment_045 486 81 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 486 40 41, g32p_row32_traceSegment_045_0486_0040, g32p_row32_traceSegment_045_0526_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0567_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 567 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0577_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 577 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0567_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 567 10 10, g32p_row32_traceSegment_045_0567_0010, g32p_row32_traceSegment_045_0577_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0587_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 587 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0597_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 597 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0587_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 587 10 10, g32p_row32_traceSegment_045_0587_0010, g32p_row32_traceSegment_045_0597_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0567_0040 : g32p_coeffSegment g32p_row32_traceSegment_045 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 567 20 20, g32p_row32_traceSegment_045_0567_0020, g32p_row32_traceSegment_045_0587_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0607_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 607 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0617_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 617 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0607_0020 : g32p_coeffSegment g32p_row32_traceSegment_045 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 607 10 10, g32p_row32_traceSegment_045_0607_0010, g32p_row32_traceSegment_045_0617_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0627_0010 : g32p_coeffSegment g32p_row32_traceSegment_045 627 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0637_0011 : g32p_coeffSegment g32p_row32_traceSegment_045 637 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_045_0627_0021 : g32p_coeffSegment g32p_row32_traceSegment_045 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 627 10 11, g32p_row32_traceSegment_045_0627_0010, g32p_row32_traceSegment_045_0637_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0607_0041 : g32p_coeffSegment g32p_row32_traceSegment_045 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 607 20 21, g32p_row32_traceSegment_045_0607_0020, g32p_row32_traceSegment_045_0627_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0567_0081 : g32p_coeffSegment g32p_row32_traceSegment_045 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 567 40 41, g32p_row32_traceSegment_045_0567_0040, g32p_row32_traceSegment_045_0607_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0486_0162 : g32p_coeffSegment g32p_row32_traceSegment_045 486 162 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 486 81 81, g32p_row32_traceSegment_045_0486_0081, g32p_row32_traceSegment_045_0567_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0324_0324 : g32p_coeffSegment g32p_row32_traceSegment_045 324 324 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 324 162 162, g32p_row32_traceSegment_045_0324_0162, g32p_row32_traceSegment_045_0486_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_045_0000_0648 : g32p_coeffSegment g32p_row32_traceSegment_045 0 648 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_045 0 324 324, g32p_row32_traceSegment_045_0000_0324, g32p_row32_traceSegment_045_0324_0324]
  decide +kernel

theorem g32p_row32_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 45 = [0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row32_traceSegment_045_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row32_traceSegment_046 (k : ℕ) : List ℤ :=
  if g32p_row32_supplierClassifier (Fin.ofNat 648 k) = 46 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row32_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row32_traceSegment_046_0000_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 0 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0010_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 10 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0000_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 0 10 10, g32p_row32_traceSegment_046_0000_0010, g32p_row32_traceSegment_046_0010_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0020_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 20 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0030_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 30 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0020_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 20 20 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 20 10 10, g32p_row32_traceSegment_046_0020_0010, g32p_row32_traceSegment_046_0030_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0000_0040 : g32p_coeffSegment g32p_row32_traceSegment_046 0 40 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 0 20 20, g32p_row32_traceSegment_046_0000_0020, g32p_row32_traceSegment_046_0020_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0040_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 40 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0050_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 50 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0040_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 40 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 40 10 10, g32p_row32_traceSegment_046_0040_0010, g32p_row32_traceSegment_046_0050_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0060_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 60 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0070_0011 : g32p_coeffSegment g32p_row32_traceSegment_046 70 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0060_0021 : g32p_coeffSegment g32p_row32_traceSegment_046 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 60 10 11, g32p_row32_traceSegment_046_0060_0010, g32p_row32_traceSegment_046_0070_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0040_0041 : g32p_coeffSegment g32p_row32_traceSegment_046 40 41 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 40 20 21, g32p_row32_traceSegment_046_0040_0020, g32p_row32_traceSegment_046_0060_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0000_0081 : g32p_coeffSegment g32p_row32_traceSegment_046 0 81 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 0 40 41, g32p_row32_traceSegment_046_0000_0040, g32p_row32_traceSegment_046_0040_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0081_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 81 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0091_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 91 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0081_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 81 10 10, g32p_row32_traceSegment_046_0081_0010, g32p_row32_traceSegment_046_0091_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0101_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 101 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0111_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 111 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0101_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 101 10 10, g32p_row32_traceSegment_046_0101_0010, g32p_row32_traceSegment_046_0111_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0081_0040 : g32p_coeffSegment g32p_row32_traceSegment_046 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 81 20 20, g32p_row32_traceSegment_046_0081_0020, g32p_row32_traceSegment_046_0101_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0121_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 121 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0131_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 131 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0121_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 121 10 10, g32p_row32_traceSegment_046_0121_0010, g32p_row32_traceSegment_046_0131_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0141_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 141 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0151_0011 : g32p_coeffSegment g32p_row32_traceSegment_046 151 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0141_0021 : g32p_coeffSegment g32p_row32_traceSegment_046 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 141 10 11, g32p_row32_traceSegment_046_0141_0010, g32p_row32_traceSegment_046_0151_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0121_0041 : g32p_coeffSegment g32p_row32_traceSegment_046 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 121 20 21, g32p_row32_traceSegment_046_0121_0020, g32p_row32_traceSegment_046_0141_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0081_0081 : g32p_coeffSegment g32p_row32_traceSegment_046 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 81 40 41, g32p_row32_traceSegment_046_0081_0040, g32p_row32_traceSegment_046_0121_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0000_0162 : g32p_coeffSegment g32p_row32_traceSegment_046 0 162 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 0 81 81, g32p_row32_traceSegment_046_0000_0081, g32p_row32_traceSegment_046_0081_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0162_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 162 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0172_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 172 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0162_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 162 10 10, g32p_row32_traceSegment_046_0162_0010, g32p_row32_traceSegment_046_0172_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0182_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 182 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0192_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 192 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0182_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 182 10 10, g32p_row32_traceSegment_046_0182_0010, g32p_row32_traceSegment_046_0192_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0162_0040 : g32p_coeffSegment g32p_row32_traceSegment_046 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 162 20 20, g32p_row32_traceSegment_046_0162_0020, g32p_row32_traceSegment_046_0182_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0202_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 202 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0212_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 212 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0202_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 202 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 202 10 10, g32p_row32_traceSegment_046_0202_0010, g32p_row32_traceSegment_046_0212_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0222_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 222 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0232_0011 : g32p_coeffSegment g32p_row32_traceSegment_046 232 11 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0222_0021 : g32p_coeffSegment g32p_row32_traceSegment_046 222 21 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 222 10 11, g32p_row32_traceSegment_046_0222_0010, g32p_row32_traceSegment_046_0232_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0202_0041 : g32p_coeffSegment g32p_row32_traceSegment_046 202 41 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 202 20 21, g32p_row32_traceSegment_046_0202_0020, g32p_row32_traceSegment_046_0222_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0162_0081 : g32p_coeffSegment g32p_row32_traceSegment_046 162 81 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 162 40 41, g32p_row32_traceSegment_046_0162_0040, g32p_row32_traceSegment_046_0202_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0243_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 243 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0253_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 253 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0243_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 243 20 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 243 10 10, g32p_row32_traceSegment_046_0243_0010, g32p_row32_traceSegment_046_0253_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0263_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 263 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0273_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 273 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0263_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 263 20 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 263 10 10, g32p_row32_traceSegment_046_0263_0010, g32p_row32_traceSegment_046_0273_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0243_0040 : g32p_coeffSegment g32p_row32_traceSegment_046 243 40 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 243 20 20, g32p_row32_traceSegment_046_0243_0020, g32p_row32_traceSegment_046_0263_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0283_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 283 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0293_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 293 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0283_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 283 20 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 283 10 10, g32p_row32_traceSegment_046_0283_0010, g32p_row32_traceSegment_046_0293_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0303_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 303 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0313_0011 : g32p_coeffSegment g32p_row32_traceSegment_046 313 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0303_0021 : g32p_coeffSegment g32p_row32_traceSegment_046 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 303 10 11, g32p_row32_traceSegment_046_0303_0010, g32p_row32_traceSegment_046_0313_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0283_0041 : g32p_coeffSegment g32p_row32_traceSegment_046 283 41 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 283 20 21, g32p_row32_traceSegment_046_0283_0020, g32p_row32_traceSegment_046_0303_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0243_0081 : g32p_coeffSegment g32p_row32_traceSegment_046 243 81 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 243 40 41, g32p_row32_traceSegment_046_0243_0040, g32p_row32_traceSegment_046_0283_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0162_0162 : g32p_coeffSegment g32p_row32_traceSegment_046 162 162 = [0, 19] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 162 81 81, g32p_row32_traceSegment_046_0162_0081, g32p_row32_traceSegment_046_0243_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0000_0324 : g32p_coeffSegment g32p_row32_traceSegment_046 0 324 = [0, 26] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 0 162 162, g32p_row32_traceSegment_046_0000_0162, g32p_row32_traceSegment_046_0162_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0324_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 324 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0334_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 334 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0324_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 324 10 10, g32p_row32_traceSegment_046_0324_0010, g32p_row32_traceSegment_046_0334_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0344_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 344 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0354_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 354 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0344_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 344 10 10, g32p_row32_traceSegment_046_0344_0010, g32p_row32_traceSegment_046_0354_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0324_0040 : g32p_coeffSegment g32p_row32_traceSegment_046 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 324 20 20, g32p_row32_traceSegment_046_0324_0020, g32p_row32_traceSegment_046_0344_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0364_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 364 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0374_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 374 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0364_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 364 10 10, g32p_row32_traceSegment_046_0364_0010, g32p_row32_traceSegment_046_0374_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0384_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 384 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0394_0011 : g32p_coeffSegment g32p_row32_traceSegment_046 394 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0384_0021 : g32p_coeffSegment g32p_row32_traceSegment_046 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 384 10 11, g32p_row32_traceSegment_046_0384_0010, g32p_row32_traceSegment_046_0394_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0364_0041 : g32p_coeffSegment g32p_row32_traceSegment_046 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 364 20 21, g32p_row32_traceSegment_046_0364_0020, g32p_row32_traceSegment_046_0384_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0324_0081 : g32p_coeffSegment g32p_row32_traceSegment_046 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 324 40 41, g32p_row32_traceSegment_046_0324_0040, g32p_row32_traceSegment_046_0364_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0405_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 405 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0415_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 415 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0405_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 405 10 10, g32p_row32_traceSegment_046_0405_0010, g32p_row32_traceSegment_046_0415_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0425_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 425 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0435_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 435 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0425_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 425 10 10, g32p_row32_traceSegment_046_0425_0010, g32p_row32_traceSegment_046_0435_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0405_0040 : g32p_coeffSegment g32p_row32_traceSegment_046 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 405 20 20, g32p_row32_traceSegment_046_0405_0020, g32p_row32_traceSegment_046_0425_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0445_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 445 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0455_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 455 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0445_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 445 10 10, g32p_row32_traceSegment_046_0445_0010, g32p_row32_traceSegment_046_0455_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0465_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 465 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0475_0011 : g32p_coeffSegment g32p_row32_traceSegment_046 475 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0465_0021 : g32p_coeffSegment g32p_row32_traceSegment_046 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 465 10 11, g32p_row32_traceSegment_046_0465_0010, g32p_row32_traceSegment_046_0475_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0445_0041 : g32p_coeffSegment g32p_row32_traceSegment_046 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 445 20 21, g32p_row32_traceSegment_046_0445_0020, g32p_row32_traceSegment_046_0465_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0405_0081 : g32p_coeffSegment g32p_row32_traceSegment_046 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 405 40 41, g32p_row32_traceSegment_046_0405_0040, g32p_row32_traceSegment_046_0445_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0324_0162 : g32p_coeffSegment g32p_row32_traceSegment_046 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 324 81 81, g32p_row32_traceSegment_046_0324_0081, g32p_row32_traceSegment_046_0405_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0486_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 486 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0496_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 496 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0486_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 486 10 10, g32p_row32_traceSegment_046_0486_0010, g32p_row32_traceSegment_046_0496_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0506_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 506 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0516_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 516 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0506_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 506 10 10, g32p_row32_traceSegment_046_0506_0010, g32p_row32_traceSegment_046_0516_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0486_0040 : g32p_coeffSegment g32p_row32_traceSegment_046 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 486 20 20, g32p_row32_traceSegment_046_0486_0020, g32p_row32_traceSegment_046_0506_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0526_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 526 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0536_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 536 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0526_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 526 10 10, g32p_row32_traceSegment_046_0526_0010, g32p_row32_traceSegment_046_0536_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0546_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 546 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0556_0011 : g32p_coeffSegment g32p_row32_traceSegment_046 556 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0546_0021 : g32p_coeffSegment g32p_row32_traceSegment_046 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 546 10 11, g32p_row32_traceSegment_046_0546_0010, g32p_row32_traceSegment_046_0556_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0526_0041 : g32p_coeffSegment g32p_row32_traceSegment_046 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 526 20 21, g32p_row32_traceSegment_046_0526_0020, g32p_row32_traceSegment_046_0546_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0486_0081 : g32p_coeffSegment g32p_row32_traceSegment_046 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 486 40 41, g32p_row32_traceSegment_046_0486_0040, g32p_row32_traceSegment_046_0526_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0567_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 567 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0577_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 577 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0567_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 567 10 10, g32p_row32_traceSegment_046_0567_0010, g32p_row32_traceSegment_046_0577_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0587_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 587 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0597_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 597 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0587_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 587 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 587 10 10, g32p_row32_traceSegment_046_0587_0010, g32p_row32_traceSegment_046_0597_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0567_0040 : g32p_coeffSegment g32p_row32_traceSegment_046 567 40 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 567 20 20, g32p_row32_traceSegment_046_0567_0020, g32p_row32_traceSegment_046_0587_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0607_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 607 10 = [0, 7] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0617_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 617 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0607_0020 : g32p_coeffSegment g32p_row32_traceSegment_046 607 20 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 607 10 10, g32p_row32_traceSegment_046_0607_0010, g32p_row32_traceSegment_046_0617_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0627_0010 : g32p_coeffSegment g32p_row32_traceSegment_046 627 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0637_0011 : g32p_coeffSegment g32p_row32_traceSegment_046 637 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_046_0627_0021 : g32p_coeffSegment g32p_row32_traceSegment_046 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 627 10 11, g32p_row32_traceSegment_046_0627_0010, g32p_row32_traceSegment_046_0637_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0607_0041 : g32p_coeffSegment g32p_row32_traceSegment_046 607 41 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 607 20 21, g32p_row32_traceSegment_046_0607_0020, g32p_row32_traceSegment_046_0627_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0567_0081 : g32p_coeffSegment g32p_row32_traceSegment_046 567 81 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 567 40 41, g32p_row32_traceSegment_046_0567_0040, g32p_row32_traceSegment_046_0607_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0486_0162 : g32p_coeffSegment g32p_row32_traceSegment_046 486 162 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 486 81 81, g32p_row32_traceSegment_046_0486_0081, g32p_row32_traceSegment_046_0567_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0324_0324 : g32p_coeffSegment g32p_row32_traceSegment_046 324 324 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 324 162 162, g32p_row32_traceSegment_046_0324_0162, g32p_row32_traceSegment_046_0486_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_046_0000_0648 : g32p_coeffSegment g32p_row32_traceSegment_046 0 648 = [0, 36] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_046 0 324 324, g32p_row32_traceSegment_046_0000_0324, g32p_row32_traceSegment_046_0324_0324]
  decide +kernel

theorem g32p_row32_traceCoefficients_046 :
    g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 46 = [0, 36] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row32_traceSegment_046_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row32_traceSegment_049 (k : ℕ) : List ℤ :=
  if g32p_row32_supplierClassifier (Fin.ofNat 648 k) = 49 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row32_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row32_traceSegment_049_0000_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 0 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0010_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 10 10 = [0, 4] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0000_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 0 20 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 0 10 10, g32p_row32_traceSegment_049_0000_0010, g32p_row32_traceSegment_049_0010_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0020_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 20 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0030_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 30 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0020_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 20 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 20 10 10, g32p_row32_traceSegment_049_0020_0010, g32p_row32_traceSegment_049_0030_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0000_0040 : g32p_coeffSegment g32p_row32_traceSegment_049 0 40 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 0 20 20, g32p_row32_traceSegment_049_0000_0020, g32p_row32_traceSegment_049_0020_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0040_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 40 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0050_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 50 10 = [0, 6] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0040_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 40 20 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 40 10 10, g32p_row32_traceSegment_049_0040_0010, g32p_row32_traceSegment_049_0050_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0060_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 60 10 = [0, 4] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0070_0011 : g32p_coeffSegment g32p_row32_traceSegment_049 70 11 = [0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0060_0021 : g32p_coeffSegment g32p_row32_traceSegment_049 60 21 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 60 10 11, g32p_row32_traceSegment_049_0060_0010, g32p_row32_traceSegment_049_0070_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0040_0041 : g32p_coeffSegment g32p_row32_traceSegment_049 40 41 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 40 20 21, g32p_row32_traceSegment_049_0040_0020, g32p_row32_traceSegment_049_0060_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0000_0081 : g32p_coeffSegment g32p_row32_traceSegment_049 0 81 = [0, 19] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 0 40 41, g32p_row32_traceSegment_049_0000_0040, g32p_row32_traceSegment_049_0040_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0081_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 81 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0091_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 91 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0081_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 81 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 81 10 10, g32p_row32_traceSegment_049_0081_0010, g32p_row32_traceSegment_049_0091_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0101_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 101 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0111_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 111 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0101_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 101 10 10, g32p_row32_traceSegment_049_0101_0010, g32p_row32_traceSegment_049_0111_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0081_0040 : g32p_coeffSegment g32p_row32_traceSegment_049 81 40 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 81 20 20, g32p_row32_traceSegment_049_0081_0020, g32p_row32_traceSegment_049_0101_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0121_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 121 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0131_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 131 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0121_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 121 20 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 121 10 10, g32p_row32_traceSegment_049_0121_0010, g32p_row32_traceSegment_049_0131_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0141_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 141 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0151_0011 : g32p_coeffSegment g32p_row32_traceSegment_049 151 11 = [0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0141_0021 : g32p_coeffSegment g32p_row32_traceSegment_049 141 21 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 141 10 11, g32p_row32_traceSegment_049_0141_0010, g32p_row32_traceSegment_049_0151_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0121_0041 : g32p_coeffSegment g32p_row32_traceSegment_049 121 41 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 121 20 21, g32p_row32_traceSegment_049_0121_0020, g32p_row32_traceSegment_049_0141_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0081_0081 : g32p_coeffSegment g32p_row32_traceSegment_049 81 81 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 81 40 41, g32p_row32_traceSegment_049_0081_0040, g32p_row32_traceSegment_049_0121_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0000_0162 : g32p_coeffSegment g32p_row32_traceSegment_049 0 162 = [0, 27] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 0 81 81, g32p_row32_traceSegment_049_0000_0081, g32p_row32_traceSegment_049_0081_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0162_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 162 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0172_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 172 10 = [0, 6] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0162_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 162 20 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 162 10 10, g32p_row32_traceSegment_049_0162_0010, g32p_row32_traceSegment_049_0172_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0182_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 182 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0192_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 192 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0182_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 182 20 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 182 10 10, g32p_row32_traceSegment_049_0182_0010, g32p_row32_traceSegment_049_0192_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0162_0040 : g32p_coeffSegment g32p_row32_traceSegment_049 162 40 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 162 20 20, g32p_row32_traceSegment_049_0162_0020, g32p_row32_traceSegment_049_0182_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0202_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 202 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0212_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 212 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0202_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 202 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 202 10 10, g32p_row32_traceSegment_049_0202_0010, g32p_row32_traceSegment_049_0212_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0222_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 222 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0232_0011 : g32p_coeffSegment g32p_row32_traceSegment_049 232 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0222_0021 : g32p_coeffSegment g32p_row32_traceSegment_049 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 222 10 11, g32p_row32_traceSegment_049_0222_0010, g32p_row32_traceSegment_049_0232_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0202_0041 : g32p_coeffSegment g32p_row32_traceSegment_049 202 41 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 202 20 21, g32p_row32_traceSegment_049_0202_0020, g32p_row32_traceSegment_049_0222_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0162_0081 : g32p_coeffSegment g32p_row32_traceSegment_049 162 81 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 162 40 41, g32p_row32_traceSegment_049_0162_0040, g32p_row32_traceSegment_049_0202_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0243_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 243 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0253_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 253 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0243_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 243 10 10, g32p_row32_traceSegment_049_0243_0010, g32p_row32_traceSegment_049_0253_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0263_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 263 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0273_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 273 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0263_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 263 10 10, g32p_row32_traceSegment_049_0263_0010, g32p_row32_traceSegment_049_0273_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0243_0040 : g32p_coeffSegment g32p_row32_traceSegment_049 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 243 20 20, g32p_row32_traceSegment_049_0243_0020, g32p_row32_traceSegment_049_0263_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0283_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 283 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0293_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 293 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0283_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 283 10 10, g32p_row32_traceSegment_049_0283_0010, g32p_row32_traceSegment_049_0293_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0303_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 303 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0313_0011 : g32p_coeffSegment g32p_row32_traceSegment_049 313 11 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0303_0021 : g32p_coeffSegment g32p_row32_traceSegment_049 303 21 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 303 10 11, g32p_row32_traceSegment_049_0303_0010, g32p_row32_traceSegment_049_0313_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0283_0041 : g32p_coeffSegment g32p_row32_traceSegment_049 283 41 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 283 20 21, g32p_row32_traceSegment_049_0283_0020, g32p_row32_traceSegment_049_0303_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0243_0081 : g32p_coeffSegment g32p_row32_traceSegment_049 243 81 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 243 40 41, g32p_row32_traceSegment_049_0243_0040, g32p_row32_traceSegment_049_0283_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0162_0162 : g32p_coeffSegment g32p_row32_traceSegment_049 162 162 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 162 81 81, g32p_row32_traceSegment_049_0162_0081, g32p_row32_traceSegment_049_0243_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0000_0324 : g32p_coeffSegment g32p_row32_traceSegment_049 0 324 = [0, 42] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 0 162 162, g32p_row32_traceSegment_049_0000_0162, g32p_row32_traceSegment_049_0162_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0324_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 324 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0334_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 334 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0324_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 324 20 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 324 10 10, g32p_row32_traceSegment_049_0324_0010, g32p_row32_traceSegment_049_0334_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0344_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 344 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0354_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 354 10 = [0, 5] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0344_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 344 20 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 344 10 10, g32p_row32_traceSegment_049_0344_0010, g32p_row32_traceSegment_049_0354_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0324_0040 : g32p_coeffSegment g32p_row32_traceSegment_049 324 40 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 324 20 20, g32p_row32_traceSegment_049_0324_0020, g32p_row32_traceSegment_049_0344_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0364_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 364 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0374_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 374 10 = [0, 6] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0364_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 364 20 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 364 10 10, g32p_row32_traceSegment_049_0364_0010, g32p_row32_traceSegment_049_0374_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0384_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 384 10 = [0, 6] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0394_0011 : g32p_coeffSegment g32p_row32_traceSegment_049 394 11 = [0, 5] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0384_0021 : g32p_coeffSegment g32p_row32_traceSegment_049 384 21 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 384 10 11, g32p_row32_traceSegment_049_0384_0010, g32p_row32_traceSegment_049_0394_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0364_0041 : g32p_coeffSegment g32p_row32_traceSegment_049 364 41 = [0, 20] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 364 20 21, g32p_row32_traceSegment_049_0364_0020, g32p_row32_traceSegment_049_0384_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0324_0081 : g32p_coeffSegment g32p_row32_traceSegment_049 324 81 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 324 40 41, g32p_row32_traceSegment_049_0324_0040, g32p_row32_traceSegment_049_0364_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0405_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 405 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0415_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 415 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0405_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 405 20 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 405 10 10, g32p_row32_traceSegment_049_0405_0010, g32p_row32_traceSegment_049_0415_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0425_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 425 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0435_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 435 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0425_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 425 10 10, g32p_row32_traceSegment_049_0425_0010, g32p_row32_traceSegment_049_0435_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0405_0040 : g32p_coeffSegment g32p_row32_traceSegment_049 405 40 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 405 20 20, g32p_row32_traceSegment_049_0405_0020, g32p_row32_traceSegment_049_0425_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0445_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 445 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0455_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 455 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0445_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 445 10 10, g32p_row32_traceSegment_049_0445_0010, g32p_row32_traceSegment_049_0455_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0465_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 465 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0475_0011 : g32p_coeffSegment g32p_row32_traceSegment_049 475 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0465_0021 : g32p_coeffSegment g32p_row32_traceSegment_049 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 465 10 11, g32p_row32_traceSegment_049_0465_0010, g32p_row32_traceSegment_049_0475_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0445_0041 : g32p_coeffSegment g32p_row32_traceSegment_049 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 445 20 21, g32p_row32_traceSegment_049_0445_0020, g32p_row32_traceSegment_049_0465_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0405_0081 : g32p_coeffSegment g32p_row32_traceSegment_049 405 81 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 405 40 41, g32p_row32_traceSegment_049_0405_0040, g32p_row32_traceSegment_049_0445_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0324_0162 : g32p_coeffSegment g32p_row32_traceSegment_049 324 162 = [0, 36] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 324 81 81, g32p_row32_traceSegment_049_0324_0081, g32p_row32_traceSegment_049_0405_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0486_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 486 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0496_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 496 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0486_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 486 10 10, g32p_row32_traceSegment_049_0486_0010, g32p_row32_traceSegment_049_0496_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0506_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 506 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0516_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 516 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0506_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 506 10 10, g32p_row32_traceSegment_049_0506_0010, g32p_row32_traceSegment_049_0516_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0486_0040 : g32p_coeffSegment g32p_row32_traceSegment_049 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 486 20 20, g32p_row32_traceSegment_049_0486_0020, g32p_row32_traceSegment_049_0506_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0526_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 526 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0536_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 536 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0526_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 526 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 526 10 10, g32p_row32_traceSegment_049_0526_0010, g32p_row32_traceSegment_049_0536_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0546_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 546 10 = [0, 7] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0556_0011 : g32p_coeffSegment g32p_row32_traceSegment_049 556 11 = [0, 8] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0546_0021 : g32p_coeffSegment g32p_row32_traceSegment_049 546 21 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 546 10 11, g32p_row32_traceSegment_049_0546_0010, g32p_row32_traceSegment_049_0556_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0526_0041 : g32p_coeffSegment g32p_row32_traceSegment_049 526 41 = [0, 17] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 526 20 21, g32p_row32_traceSegment_049_0526_0020, g32p_row32_traceSegment_049_0546_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0486_0081 : g32p_coeffSegment g32p_row32_traceSegment_049 486 81 = [0, 17] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 486 40 41, g32p_row32_traceSegment_049_0486_0040, g32p_row32_traceSegment_049_0526_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0567_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 567 10 = [0, 6] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0577_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 577 10 = [0, 5] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0567_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 567 20 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 567 10 10, g32p_row32_traceSegment_049_0567_0010, g32p_row32_traceSegment_049_0577_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0587_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 587 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0597_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 597 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0587_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 587 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 587 10 10, g32p_row32_traceSegment_049_0587_0010, g32p_row32_traceSegment_049_0597_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0567_0040 : g32p_coeffSegment g32p_row32_traceSegment_049 567 40 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 567 20 20, g32p_row32_traceSegment_049_0567_0020, g32p_row32_traceSegment_049_0587_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0607_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 607 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0617_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 617 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0607_0020 : g32p_coeffSegment g32p_row32_traceSegment_049 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 607 10 10, g32p_row32_traceSegment_049_0607_0010, g32p_row32_traceSegment_049_0617_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0627_0010 : g32p_coeffSegment g32p_row32_traceSegment_049 627 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0637_0011 : g32p_coeffSegment g32p_row32_traceSegment_049 637 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_049_0627_0021 : g32p_coeffSegment g32p_row32_traceSegment_049 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 627 10 11, g32p_row32_traceSegment_049_0627_0010, g32p_row32_traceSegment_049_0637_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0607_0041 : g32p_coeffSegment g32p_row32_traceSegment_049 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 607 20 21, g32p_row32_traceSegment_049_0607_0020, g32p_row32_traceSegment_049_0627_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0567_0081 : g32p_coeffSegment g32p_row32_traceSegment_049 567 81 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 567 40 41, g32p_row32_traceSegment_049_0567_0040, g32p_row32_traceSegment_049_0607_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0486_0162 : g32p_coeffSegment g32p_row32_traceSegment_049 486 162 = [0, 30] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 486 81 81, g32p_row32_traceSegment_049_0486_0081, g32p_row32_traceSegment_049_0567_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0324_0324 : g32p_coeffSegment g32p_row32_traceSegment_049 324 324 = [0, 66] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 324 162 162, g32p_row32_traceSegment_049_0324_0162, g32p_row32_traceSegment_049_0486_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_049_0000_0648 : g32p_coeffSegment g32p_row32_traceSegment_049 0 648 = [0, 108] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_049 0 324 324, g32p_row32_traceSegment_049_0000_0324, g32p_row32_traceSegment_049_0324_0324]
  decide +kernel

theorem g32p_row32_traceCoefficients_049 :
    g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 49 = [0, 108] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row32_traceSegment_049_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row32_traceSegment_056 (k : ℕ) : List ℤ :=
  if g32p_row32_supplierClassifier (Fin.ofNat 648 k) = 56 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row32_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row32_traceSegment_056_0000_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 0 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0010_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 10 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0000_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 0 10 10, g32p_row32_traceSegment_056_0000_0010, g32p_row32_traceSegment_056_0010_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0020_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 20 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0030_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 30 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0020_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 20 10 10, g32p_row32_traceSegment_056_0020_0010, g32p_row32_traceSegment_056_0030_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0000_0040 : g32p_coeffSegment g32p_row32_traceSegment_056 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 0 20 20, g32p_row32_traceSegment_056_0000_0020, g32p_row32_traceSegment_056_0020_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0040_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 40 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0050_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 50 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0040_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 40 10 10, g32p_row32_traceSegment_056_0040_0010, g32p_row32_traceSegment_056_0050_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0060_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 60 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0070_0011 : g32p_coeffSegment g32p_row32_traceSegment_056 70 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0060_0021 : g32p_coeffSegment g32p_row32_traceSegment_056 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 60 10 11, g32p_row32_traceSegment_056_0060_0010, g32p_row32_traceSegment_056_0070_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0040_0041 : g32p_coeffSegment g32p_row32_traceSegment_056 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 40 20 21, g32p_row32_traceSegment_056_0040_0020, g32p_row32_traceSegment_056_0060_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0000_0081 : g32p_coeffSegment g32p_row32_traceSegment_056 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 0 40 41, g32p_row32_traceSegment_056_0000_0040, g32p_row32_traceSegment_056_0040_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0081_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 81 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0091_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 91 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0081_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 81 10 10, g32p_row32_traceSegment_056_0081_0010, g32p_row32_traceSegment_056_0091_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0101_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 101 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0111_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 111 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0101_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 101 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 101 10 10, g32p_row32_traceSegment_056_0101_0010, g32p_row32_traceSegment_056_0111_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0081_0040 : g32p_coeffSegment g32p_row32_traceSegment_056 81 40 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 81 20 20, g32p_row32_traceSegment_056_0081_0020, g32p_row32_traceSegment_056_0101_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0121_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 121 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0131_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 131 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0121_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 121 10 10, g32p_row32_traceSegment_056_0121_0010, g32p_row32_traceSegment_056_0131_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0141_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 141 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0151_0011 : g32p_coeffSegment g32p_row32_traceSegment_056 151 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0141_0021 : g32p_coeffSegment g32p_row32_traceSegment_056 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 141 10 11, g32p_row32_traceSegment_056_0141_0010, g32p_row32_traceSegment_056_0151_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0121_0041 : g32p_coeffSegment g32p_row32_traceSegment_056 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 121 20 21, g32p_row32_traceSegment_056_0121_0020, g32p_row32_traceSegment_056_0141_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0081_0081 : g32p_coeffSegment g32p_row32_traceSegment_056 81 81 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 81 40 41, g32p_row32_traceSegment_056_0081_0040, g32p_row32_traceSegment_056_0121_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0000_0162 : g32p_coeffSegment g32p_row32_traceSegment_056 0 162 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 0 81 81, g32p_row32_traceSegment_056_0000_0081, g32p_row32_traceSegment_056_0081_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0162_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 162 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0172_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 172 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0162_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 162 10 10, g32p_row32_traceSegment_056_0162_0010, g32p_row32_traceSegment_056_0172_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0182_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 182 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0192_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 192 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0182_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 182 10 10, g32p_row32_traceSegment_056_0182_0010, g32p_row32_traceSegment_056_0192_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0162_0040 : g32p_coeffSegment g32p_row32_traceSegment_056 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 162 20 20, g32p_row32_traceSegment_056_0162_0020, g32p_row32_traceSegment_056_0182_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0202_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 202 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0212_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 212 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0202_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 202 10 10, g32p_row32_traceSegment_056_0202_0010, g32p_row32_traceSegment_056_0212_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0222_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 222 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0232_0011 : g32p_coeffSegment g32p_row32_traceSegment_056 232 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0222_0021 : g32p_coeffSegment g32p_row32_traceSegment_056 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 222 10 11, g32p_row32_traceSegment_056_0222_0010, g32p_row32_traceSegment_056_0232_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0202_0041 : g32p_coeffSegment g32p_row32_traceSegment_056 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 202 20 21, g32p_row32_traceSegment_056_0202_0020, g32p_row32_traceSegment_056_0222_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0162_0081 : g32p_coeffSegment g32p_row32_traceSegment_056 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 162 40 41, g32p_row32_traceSegment_056_0162_0040, g32p_row32_traceSegment_056_0202_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0243_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 243 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0253_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 253 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0243_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 243 10 10, g32p_row32_traceSegment_056_0243_0010, g32p_row32_traceSegment_056_0253_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0263_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 263 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0273_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 273 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0263_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 263 10 10, g32p_row32_traceSegment_056_0263_0010, g32p_row32_traceSegment_056_0273_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0243_0040 : g32p_coeffSegment g32p_row32_traceSegment_056 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 243 20 20, g32p_row32_traceSegment_056_0243_0020, g32p_row32_traceSegment_056_0263_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0283_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 283 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0293_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 293 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0283_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 283 10 10, g32p_row32_traceSegment_056_0283_0010, g32p_row32_traceSegment_056_0293_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0303_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 303 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0313_0011 : g32p_coeffSegment g32p_row32_traceSegment_056 313 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0303_0021 : g32p_coeffSegment g32p_row32_traceSegment_056 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 303 10 11, g32p_row32_traceSegment_056_0303_0010, g32p_row32_traceSegment_056_0313_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0283_0041 : g32p_coeffSegment g32p_row32_traceSegment_056 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 283 20 21, g32p_row32_traceSegment_056_0283_0020, g32p_row32_traceSegment_056_0303_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0243_0081 : g32p_coeffSegment g32p_row32_traceSegment_056 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 243 40 41, g32p_row32_traceSegment_056_0243_0040, g32p_row32_traceSegment_056_0283_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0162_0162 : g32p_coeffSegment g32p_row32_traceSegment_056 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 162 81 81, g32p_row32_traceSegment_056_0162_0081, g32p_row32_traceSegment_056_0243_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0000_0324 : g32p_coeffSegment g32p_row32_traceSegment_056 0 324 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 0 162 162, g32p_row32_traceSegment_056_0000_0162, g32p_row32_traceSegment_056_0162_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0324_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 324 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0334_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 334 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0324_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 324 10 10, g32p_row32_traceSegment_056_0324_0010, g32p_row32_traceSegment_056_0334_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0344_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 344 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0354_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 354 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0344_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 344 10 10, g32p_row32_traceSegment_056_0344_0010, g32p_row32_traceSegment_056_0354_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0324_0040 : g32p_coeffSegment g32p_row32_traceSegment_056 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 324 20 20, g32p_row32_traceSegment_056_0324_0020, g32p_row32_traceSegment_056_0344_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0364_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 364 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0374_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 374 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0364_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 364 10 10, g32p_row32_traceSegment_056_0364_0010, g32p_row32_traceSegment_056_0374_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0384_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 384 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0394_0011 : g32p_coeffSegment g32p_row32_traceSegment_056 394 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0384_0021 : g32p_coeffSegment g32p_row32_traceSegment_056 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 384 10 11, g32p_row32_traceSegment_056_0384_0010, g32p_row32_traceSegment_056_0394_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0364_0041 : g32p_coeffSegment g32p_row32_traceSegment_056 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 364 20 21, g32p_row32_traceSegment_056_0364_0020, g32p_row32_traceSegment_056_0384_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0324_0081 : g32p_coeffSegment g32p_row32_traceSegment_056 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 324 40 41, g32p_row32_traceSegment_056_0324_0040, g32p_row32_traceSegment_056_0364_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0405_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 405 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0415_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 415 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0405_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 405 10 10, g32p_row32_traceSegment_056_0405_0010, g32p_row32_traceSegment_056_0415_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0425_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 425 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0435_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 435 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0425_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 425 10 10, g32p_row32_traceSegment_056_0425_0010, g32p_row32_traceSegment_056_0435_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0405_0040 : g32p_coeffSegment g32p_row32_traceSegment_056 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 405 20 20, g32p_row32_traceSegment_056_0405_0020, g32p_row32_traceSegment_056_0425_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0445_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 445 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0455_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 455 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0445_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 445 10 10, g32p_row32_traceSegment_056_0445_0010, g32p_row32_traceSegment_056_0455_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0465_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 465 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0475_0011 : g32p_coeffSegment g32p_row32_traceSegment_056 475 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0465_0021 : g32p_coeffSegment g32p_row32_traceSegment_056 465 21 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 465 10 11, g32p_row32_traceSegment_056_0465_0010, g32p_row32_traceSegment_056_0475_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0445_0041 : g32p_coeffSegment g32p_row32_traceSegment_056 445 41 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 445 20 21, g32p_row32_traceSegment_056_0445_0020, g32p_row32_traceSegment_056_0465_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0405_0081 : g32p_coeffSegment g32p_row32_traceSegment_056 405 81 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 405 40 41, g32p_row32_traceSegment_056_0405_0040, g32p_row32_traceSegment_056_0445_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0324_0162 : g32p_coeffSegment g32p_row32_traceSegment_056 324 162 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 324 81 81, g32p_row32_traceSegment_056_0324_0081, g32p_row32_traceSegment_056_0405_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0486_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 486 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0496_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 496 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0486_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 486 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 486 10 10, g32p_row32_traceSegment_056_0486_0010, g32p_row32_traceSegment_056_0496_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0506_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 506 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0516_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 516 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0506_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 506 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 506 10 10, g32p_row32_traceSegment_056_0506_0010, g32p_row32_traceSegment_056_0516_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0486_0040 : g32p_coeffSegment g32p_row32_traceSegment_056 486 40 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 486 20 20, g32p_row32_traceSegment_056_0486_0020, g32p_row32_traceSegment_056_0506_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0526_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 526 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0536_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 536 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0526_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 526 10 10, g32p_row32_traceSegment_056_0526_0010, g32p_row32_traceSegment_056_0536_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0546_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 546 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0556_0011 : g32p_coeffSegment g32p_row32_traceSegment_056 556 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0546_0021 : g32p_coeffSegment g32p_row32_traceSegment_056 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 546 10 11, g32p_row32_traceSegment_056_0546_0010, g32p_row32_traceSegment_056_0556_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0526_0041 : g32p_coeffSegment g32p_row32_traceSegment_056 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 526 20 21, g32p_row32_traceSegment_056_0526_0020, g32p_row32_traceSegment_056_0546_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0486_0081 : g32p_coeffSegment g32p_row32_traceSegment_056 486 81 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 486 40 41, g32p_row32_traceSegment_056_0486_0040, g32p_row32_traceSegment_056_0526_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0567_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 567 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0577_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 577 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0567_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 567 10 10, g32p_row32_traceSegment_056_0567_0010, g32p_row32_traceSegment_056_0577_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0587_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 587 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0597_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 597 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0587_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 587 10 10, g32p_row32_traceSegment_056_0587_0010, g32p_row32_traceSegment_056_0597_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0567_0040 : g32p_coeffSegment g32p_row32_traceSegment_056 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 567 20 20, g32p_row32_traceSegment_056_0567_0020, g32p_row32_traceSegment_056_0587_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0607_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 607 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0617_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 617 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0607_0020 : g32p_coeffSegment g32p_row32_traceSegment_056 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 607 10 10, g32p_row32_traceSegment_056_0607_0010, g32p_row32_traceSegment_056_0617_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0627_0010 : g32p_coeffSegment g32p_row32_traceSegment_056 627 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0637_0011 : g32p_coeffSegment g32p_row32_traceSegment_056 637 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_056_0627_0021 : g32p_coeffSegment g32p_row32_traceSegment_056 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 627 10 11, g32p_row32_traceSegment_056_0627_0010, g32p_row32_traceSegment_056_0637_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0607_0041 : g32p_coeffSegment g32p_row32_traceSegment_056 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 607 20 21, g32p_row32_traceSegment_056_0607_0020, g32p_row32_traceSegment_056_0627_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0567_0081 : g32p_coeffSegment g32p_row32_traceSegment_056 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 567 40 41, g32p_row32_traceSegment_056_0567_0040, g32p_row32_traceSegment_056_0607_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0486_0162 : g32p_coeffSegment g32p_row32_traceSegment_056 486 162 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 486 81 81, g32p_row32_traceSegment_056_0486_0081, g32p_row32_traceSegment_056_0567_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0324_0324 : g32p_coeffSegment g32p_row32_traceSegment_056 324 324 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 324 162 162, g32p_row32_traceSegment_056_0324_0162, g32p_row32_traceSegment_056_0486_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_056_0000_0648 : g32p_coeffSegment g32p_row32_traceSegment_056 0 648 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_056 0 324 324, g32p_row32_traceSegment_056_0000_0324, g32p_row32_traceSegment_056_0324_0324]
  decide +kernel

theorem g32p_row32_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 56 = [0, 6] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row32_traceSegment_056_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row32_traceSegment_057 (k : ℕ) : List ℤ :=
  if g32p_row32_supplierClassifier (Fin.ofNat 648 k) = 57 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row32_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row32_traceSegment_057_0000_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 0 10 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0010_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 10 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0000_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 0 20 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 0 10 10, g32p_row32_traceSegment_057_0000_0010, g32p_row32_traceSegment_057_0010_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0020_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 20 10 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0030_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 30 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0020_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 20 20 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 20 10 10, g32p_row32_traceSegment_057_0020_0010, g32p_row32_traceSegment_057_0030_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0000_0040 : g32p_coeffSegment g32p_row32_traceSegment_057 0 40 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 0 20 20, g32p_row32_traceSegment_057_0000_0020, g32p_row32_traceSegment_057_0020_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0040_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 40 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0050_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 50 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0040_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 40 10 10, g32p_row32_traceSegment_057_0040_0010, g32p_row32_traceSegment_057_0050_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0060_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 60 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0070_0011 : g32p_coeffSegment g32p_row32_traceSegment_057 70 11 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0060_0021 : g32p_coeffSegment g32p_row32_traceSegment_057 60 21 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 60 10 11, g32p_row32_traceSegment_057_0060_0010, g32p_row32_traceSegment_057_0070_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0040_0041 : g32p_coeffSegment g32p_row32_traceSegment_057 40 41 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 40 20 21, g32p_row32_traceSegment_057_0040_0020, g32p_row32_traceSegment_057_0060_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0000_0081 : g32p_coeffSegment g32p_row32_traceSegment_057 0 81 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 0 40 41, g32p_row32_traceSegment_057_0000_0040, g32p_row32_traceSegment_057_0040_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0081_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 81 10 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0091_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 91 10 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0081_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 81 20 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 81 10 10, g32p_row32_traceSegment_057_0081_0010, g32p_row32_traceSegment_057_0091_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0101_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 101 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0111_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 111 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0101_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 101 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 101 10 10, g32p_row32_traceSegment_057_0101_0010, g32p_row32_traceSegment_057_0111_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0081_0040 : g32p_coeffSegment g32p_row32_traceSegment_057 81 40 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 81 20 20, g32p_row32_traceSegment_057_0081_0020, g32p_row32_traceSegment_057_0101_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0121_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 121 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0131_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 131 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0121_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 121 10 10, g32p_row32_traceSegment_057_0121_0010, g32p_row32_traceSegment_057_0131_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0141_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 141 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0151_0011 : g32p_coeffSegment g32p_row32_traceSegment_057 151 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0141_0021 : g32p_coeffSegment g32p_row32_traceSegment_057 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 141 10 11, g32p_row32_traceSegment_057_0141_0010, g32p_row32_traceSegment_057_0151_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0121_0041 : g32p_coeffSegment g32p_row32_traceSegment_057 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 121 20 21, g32p_row32_traceSegment_057_0121_0020, g32p_row32_traceSegment_057_0141_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0081_0081 : g32p_coeffSegment g32p_row32_traceSegment_057 81 81 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 81 40 41, g32p_row32_traceSegment_057_0081_0040, g32p_row32_traceSegment_057_0121_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0000_0162 : g32p_coeffSegment g32p_row32_traceSegment_057 0 162 = [0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 0 81 81, g32p_row32_traceSegment_057_0000_0081, g32p_row32_traceSegment_057_0081_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0162_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 162 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0172_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 172 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0162_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 162 10 10, g32p_row32_traceSegment_057_0162_0010, g32p_row32_traceSegment_057_0172_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0182_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 182 10 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0192_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 192 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0182_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 182 20 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 182 10 10, g32p_row32_traceSegment_057_0182_0010, g32p_row32_traceSegment_057_0192_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0162_0040 : g32p_coeffSegment g32p_row32_traceSegment_057 162 40 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 162 20 20, g32p_row32_traceSegment_057_0162_0020, g32p_row32_traceSegment_057_0182_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0202_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 202 10 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0212_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 212 10 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0202_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 202 20 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 202 10 10, g32p_row32_traceSegment_057_0202_0010, g32p_row32_traceSegment_057_0212_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0222_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 222 10 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0232_0011 : g32p_coeffSegment g32p_row32_traceSegment_057 232 11 = [0, 0, 6] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0222_0021 : g32p_coeffSegment g32p_row32_traceSegment_057 222 21 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 222 10 11, g32p_row32_traceSegment_057_0222_0010, g32p_row32_traceSegment_057_0232_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0202_0041 : g32p_coeffSegment g32p_row32_traceSegment_057 202 41 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 202 20 21, g32p_row32_traceSegment_057_0202_0020, g32p_row32_traceSegment_057_0222_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0162_0081 : g32p_coeffSegment g32p_row32_traceSegment_057 162 81 = [0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 162 40 41, g32p_row32_traceSegment_057_0162_0040, g32p_row32_traceSegment_057_0202_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0243_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 243 10 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0253_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 253 10 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0243_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 243 20 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 243 10 10, g32p_row32_traceSegment_057_0243_0010, g32p_row32_traceSegment_057_0253_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0263_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 263 10 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0273_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 273 10 = [0, 0, 7] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0263_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 263 20 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 263 10 10, g32p_row32_traceSegment_057_0263_0010, g32p_row32_traceSegment_057_0273_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0243_0040 : g32p_coeffSegment g32p_row32_traceSegment_057 243 40 = [0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 243 20 20, g32p_row32_traceSegment_057_0243_0020, g32p_row32_traceSegment_057_0263_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0283_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 283 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0293_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 293 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0283_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 283 10 10, g32p_row32_traceSegment_057_0283_0010, g32p_row32_traceSegment_057_0293_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0303_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 303 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0313_0011 : g32p_coeffSegment g32p_row32_traceSegment_057 313 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0303_0021 : g32p_coeffSegment g32p_row32_traceSegment_057 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 303 10 11, g32p_row32_traceSegment_057_0303_0010, g32p_row32_traceSegment_057_0313_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0283_0041 : g32p_coeffSegment g32p_row32_traceSegment_057 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 283 20 21, g32p_row32_traceSegment_057_0283_0020, g32p_row32_traceSegment_057_0303_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0243_0081 : g32p_coeffSegment g32p_row32_traceSegment_057 243 81 = [0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 243 40 41, g32p_row32_traceSegment_057_0243_0040, g32p_row32_traceSegment_057_0283_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0162_0162 : g32p_coeffSegment g32p_row32_traceSegment_057 162 162 = [0, 0, 43] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 162 81 81, g32p_row32_traceSegment_057_0162_0081, g32p_row32_traceSegment_057_0243_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0000_0324 : g32p_coeffSegment g32p_row32_traceSegment_057 0 324 = [0, 0, 62] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 0 162 162, g32p_row32_traceSegment_057_0000_0162, g32p_row32_traceSegment_057_0162_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0324_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 324 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0334_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 334 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0324_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 324 10 10, g32p_row32_traceSegment_057_0324_0010, g32p_row32_traceSegment_057_0334_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0344_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 344 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0354_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 354 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0344_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 344 10 10, g32p_row32_traceSegment_057_0344_0010, g32p_row32_traceSegment_057_0354_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0324_0040 : g32p_coeffSegment g32p_row32_traceSegment_057 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 324 20 20, g32p_row32_traceSegment_057_0324_0020, g32p_row32_traceSegment_057_0344_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0364_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 364 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0374_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 374 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0364_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 364 10 10, g32p_row32_traceSegment_057_0364_0010, g32p_row32_traceSegment_057_0374_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0384_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 384 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0394_0011 : g32p_coeffSegment g32p_row32_traceSegment_057 394 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0384_0021 : g32p_coeffSegment g32p_row32_traceSegment_057 384 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 384 10 11, g32p_row32_traceSegment_057_0384_0010, g32p_row32_traceSegment_057_0394_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0364_0041 : g32p_coeffSegment g32p_row32_traceSegment_057 364 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 364 20 21, g32p_row32_traceSegment_057_0364_0020, g32p_row32_traceSegment_057_0384_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0324_0081 : g32p_coeffSegment g32p_row32_traceSegment_057 324 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 324 40 41, g32p_row32_traceSegment_057_0324_0040, g32p_row32_traceSegment_057_0364_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0405_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 405 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0415_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 415 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0405_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 405 20 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 405 10 10, g32p_row32_traceSegment_057_0405_0010, g32p_row32_traceSegment_057_0415_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0425_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 425 10 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0435_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 435 10 = [0, 0, 6] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0425_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 425 20 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 425 10 10, g32p_row32_traceSegment_057_0425_0010, g32p_row32_traceSegment_057_0435_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0405_0040 : g32p_coeffSegment g32p_row32_traceSegment_057 405 40 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 405 20 20, g32p_row32_traceSegment_057_0405_0020, g32p_row32_traceSegment_057_0425_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0445_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 445 10 = [0, 0, 7] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0455_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 455 10 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0445_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 445 20 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 445 10 10, g32p_row32_traceSegment_057_0445_0010, g32p_row32_traceSegment_057_0455_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0465_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 465 10 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0475_0011 : g32p_coeffSegment g32p_row32_traceSegment_057 475 11 = [0, 0, 6] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0465_0021 : g32p_coeffSegment g32p_row32_traceSegment_057 465 21 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 465 10 11, g32p_row32_traceSegment_057_0465_0010, g32p_row32_traceSegment_057_0475_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0445_0041 : g32p_coeffSegment g32p_row32_traceSegment_057 445 41 = [0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 445 20 21, g32p_row32_traceSegment_057_0445_0020, g32p_row32_traceSegment_057_0465_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0405_0081 : g32p_coeffSegment g32p_row32_traceSegment_057 405 81 = [0, 0, 35] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 405 40 41, g32p_row32_traceSegment_057_0405_0040, g32p_row32_traceSegment_057_0445_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0324_0162 : g32p_coeffSegment g32p_row32_traceSegment_057 324 162 = [0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 324 81 81, g32p_row32_traceSegment_057_0324_0081, g32p_row32_traceSegment_057_0405_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0486_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 486 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0496_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 496 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0486_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 486 10 10, g32p_row32_traceSegment_057_0486_0010, g32p_row32_traceSegment_057_0496_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0506_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 506 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0516_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 516 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0506_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 506 10 10, g32p_row32_traceSegment_057_0506_0010, g32p_row32_traceSegment_057_0516_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0486_0040 : g32p_coeffSegment g32p_row32_traceSegment_057 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 486 20 20, g32p_row32_traceSegment_057_0486_0020, g32p_row32_traceSegment_057_0506_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0526_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 526 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0536_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 536 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0526_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 526 10 10, g32p_row32_traceSegment_057_0526_0010, g32p_row32_traceSegment_057_0536_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0546_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 546 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0556_0011 : g32p_coeffSegment g32p_row32_traceSegment_057 556 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0546_0021 : g32p_coeffSegment g32p_row32_traceSegment_057 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 546 10 11, g32p_row32_traceSegment_057_0546_0010, g32p_row32_traceSegment_057_0556_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0526_0041 : g32p_coeffSegment g32p_row32_traceSegment_057 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 526 20 21, g32p_row32_traceSegment_057_0526_0020, g32p_row32_traceSegment_057_0546_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0486_0081 : g32p_coeffSegment g32p_row32_traceSegment_057 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 486 40 41, g32p_row32_traceSegment_057_0486_0040, g32p_row32_traceSegment_057_0526_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0567_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 567 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0577_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 577 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0567_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 567 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 567 10 10, g32p_row32_traceSegment_057_0567_0010, g32p_row32_traceSegment_057_0577_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0587_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 587 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0597_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 597 10 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0587_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 587 20 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 587 10 10, g32p_row32_traceSegment_057_0587_0010, g32p_row32_traceSegment_057_0597_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0567_0040 : g32p_coeffSegment g32p_row32_traceSegment_057 567 40 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 567 20 20, g32p_row32_traceSegment_057_0567_0020, g32p_row32_traceSegment_057_0587_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0607_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 607 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0617_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 617 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0607_0020 : g32p_coeffSegment g32p_row32_traceSegment_057 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 607 10 10, g32p_row32_traceSegment_057_0607_0010, g32p_row32_traceSegment_057_0617_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0627_0010 : g32p_coeffSegment g32p_row32_traceSegment_057 627 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0637_0011 : g32p_coeffSegment g32p_row32_traceSegment_057 637 11 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row32_traceSegment_057_0627_0021 : g32p_coeffSegment g32p_row32_traceSegment_057 627 21 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 627 10 11, g32p_row32_traceSegment_057_0627_0010, g32p_row32_traceSegment_057_0637_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0607_0041 : g32p_coeffSegment g32p_row32_traceSegment_057 607 41 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 607 20 21, g32p_row32_traceSegment_057_0607_0020, g32p_row32_traceSegment_057_0627_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0567_0081 : g32p_coeffSegment g32p_row32_traceSegment_057 567 81 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 567 40 41, g32p_row32_traceSegment_057_0567_0040, g32p_row32_traceSegment_057_0607_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0486_0162 : g32p_coeffSegment g32p_row32_traceSegment_057 486 162 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 486 81 81, g32p_row32_traceSegment_057_0486_0081, g32p_row32_traceSegment_057_0567_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0324_0324 : g32p_coeffSegment g32p_row32_traceSegment_057 324 324 = [0, 0, 46] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 324 162 162, g32p_row32_traceSegment_057_0324_0162, g32p_row32_traceSegment_057_0486_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_057_0000_0648 : g32p_coeffSegment g32p_row32_traceSegment_057 0 648 = [0, 0, 108] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_057 0 324 324, g32p_row32_traceSegment_057_0000_0324, g32p_row32_traceSegment_057_0324_0324]
  decide +kernel

theorem g32p_row32_traceCoefficients_057 :
    g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 57 = [0, 0, 108] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row32_traceSegment_057_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row32_traceSegment_067 (k : ℕ) : List ℤ :=
  if g32p_row32_supplierClassifier (Fin.ofNat 648 k) = 67 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row32_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row32_traceSegment_067_0000_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 0 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0010_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 10 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0000_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 0 10 10, g32p_row32_traceSegment_067_0000_0010, g32p_row32_traceSegment_067_0010_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0020_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 20 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0030_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 30 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0020_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 20 10 10, g32p_row32_traceSegment_067_0020_0010, g32p_row32_traceSegment_067_0030_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0000_0040 : g32p_coeffSegment g32p_row32_traceSegment_067 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 0 20 20, g32p_row32_traceSegment_067_0000_0020, g32p_row32_traceSegment_067_0020_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0040_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 40 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0050_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 50 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0040_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 40 10 10, g32p_row32_traceSegment_067_0040_0010, g32p_row32_traceSegment_067_0050_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0060_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 60 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0070_0011 : g32p_coeffSegment g32p_row32_traceSegment_067 70 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0060_0021 : g32p_coeffSegment g32p_row32_traceSegment_067 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 60 10 11, g32p_row32_traceSegment_067_0060_0010, g32p_row32_traceSegment_067_0070_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0040_0041 : g32p_coeffSegment g32p_row32_traceSegment_067 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 40 20 21, g32p_row32_traceSegment_067_0040_0020, g32p_row32_traceSegment_067_0060_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0000_0081 : g32p_coeffSegment g32p_row32_traceSegment_067 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 0 40 41, g32p_row32_traceSegment_067_0000_0040, g32p_row32_traceSegment_067_0040_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0081_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 81 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0091_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 91 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0081_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 81 10 10, g32p_row32_traceSegment_067_0081_0010, g32p_row32_traceSegment_067_0091_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0101_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 101 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0111_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 111 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0101_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 101 10 10, g32p_row32_traceSegment_067_0101_0010, g32p_row32_traceSegment_067_0111_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0081_0040 : g32p_coeffSegment g32p_row32_traceSegment_067 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 81 20 20, g32p_row32_traceSegment_067_0081_0020, g32p_row32_traceSegment_067_0101_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0121_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 121 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0131_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 131 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0121_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 121 10 10, g32p_row32_traceSegment_067_0121_0010, g32p_row32_traceSegment_067_0131_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0141_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 141 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0151_0011 : g32p_coeffSegment g32p_row32_traceSegment_067 151 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0141_0021 : g32p_coeffSegment g32p_row32_traceSegment_067 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 141 10 11, g32p_row32_traceSegment_067_0141_0010, g32p_row32_traceSegment_067_0151_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0121_0041 : g32p_coeffSegment g32p_row32_traceSegment_067 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 121 20 21, g32p_row32_traceSegment_067_0121_0020, g32p_row32_traceSegment_067_0141_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0081_0081 : g32p_coeffSegment g32p_row32_traceSegment_067 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 81 40 41, g32p_row32_traceSegment_067_0081_0040, g32p_row32_traceSegment_067_0121_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0000_0162 : g32p_coeffSegment g32p_row32_traceSegment_067 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 0 81 81, g32p_row32_traceSegment_067_0000_0081, g32p_row32_traceSegment_067_0081_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0162_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 162 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0172_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 172 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0162_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 162 10 10, g32p_row32_traceSegment_067_0162_0010, g32p_row32_traceSegment_067_0172_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0182_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 182 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0192_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 192 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0182_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 182 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 182 10 10, g32p_row32_traceSegment_067_0182_0010, g32p_row32_traceSegment_067_0192_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0162_0040 : g32p_coeffSegment g32p_row32_traceSegment_067 162 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 162 20 20, g32p_row32_traceSegment_067_0162_0020, g32p_row32_traceSegment_067_0182_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0202_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 202 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0212_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 212 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0202_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 202 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 202 10 10, g32p_row32_traceSegment_067_0202_0010, g32p_row32_traceSegment_067_0212_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0222_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 222 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0232_0011 : g32p_coeffSegment g32p_row32_traceSegment_067 232 11 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0222_0021 : g32p_coeffSegment g32p_row32_traceSegment_067 222 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 222 10 11, g32p_row32_traceSegment_067_0222_0010, g32p_row32_traceSegment_067_0232_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0202_0041 : g32p_coeffSegment g32p_row32_traceSegment_067 202 41 = [3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 202 20 21, g32p_row32_traceSegment_067_0202_0020, g32p_row32_traceSegment_067_0222_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0162_0081 : g32p_coeffSegment g32p_row32_traceSegment_067 162 81 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 162 40 41, g32p_row32_traceSegment_067_0162_0040, g32p_row32_traceSegment_067_0202_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0243_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 243 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0253_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 253 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0243_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 243 10 10, g32p_row32_traceSegment_067_0243_0010, g32p_row32_traceSegment_067_0253_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0263_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 263 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0273_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 273 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0263_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 263 10 10, g32p_row32_traceSegment_067_0263_0010, g32p_row32_traceSegment_067_0273_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0243_0040 : g32p_coeffSegment g32p_row32_traceSegment_067 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 243 20 20, g32p_row32_traceSegment_067_0243_0020, g32p_row32_traceSegment_067_0263_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0283_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 283 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0293_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 293 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0283_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 283 10 10, g32p_row32_traceSegment_067_0283_0010, g32p_row32_traceSegment_067_0293_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0303_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 303 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0313_0011 : g32p_coeffSegment g32p_row32_traceSegment_067 313 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0303_0021 : g32p_coeffSegment g32p_row32_traceSegment_067 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 303 10 11, g32p_row32_traceSegment_067_0303_0010, g32p_row32_traceSegment_067_0313_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0283_0041 : g32p_coeffSegment g32p_row32_traceSegment_067 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 283 20 21, g32p_row32_traceSegment_067_0283_0020, g32p_row32_traceSegment_067_0303_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0243_0081 : g32p_coeffSegment g32p_row32_traceSegment_067 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 243 40 41, g32p_row32_traceSegment_067_0243_0040, g32p_row32_traceSegment_067_0283_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0162_0162 : g32p_coeffSegment g32p_row32_traceSegment_067 162 162 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 162 81 81, g32p_row32_traceSegment_067_0162_0081, g32p_row32_traceSegment_067_0243_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0000_0324 : g32p_coeffSegment g32p_row32_traceSegment_067 0 324 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 0 162 162, g32p_row32_traceSegment_067_0000_0162, g32p_row32_traceSegment_067_0162_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0324_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 324 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0334_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 334 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0324_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 324 10 10, g32p_row32_traceSegment_067_0324_0010, g32p_row32_traceSegment_067_0334_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0344_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 344 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0354_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 354 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0344_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 344 10 10, g32p_row32_traceSegment_067_0344_0010, g32p_row32_traceSegment_067_0354_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0324_0040 : g32p_coeffSegment g32p_row32_traceSegment_067 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 324 20 20, g32p_row32_traceSegment_067_0324_0020, g32p_row32_traceSegment_067_0344_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0364_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 364 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0374_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 374 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0364_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 364 10 10, g32p_row32_traceSegment_067_0364_0010, g32p_row32_traceSegment_067_0374_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0384_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 384 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0394_0011 : g32p_coeffSegment g32p_row32_traceSegment_067 394 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0384_0021 : g32p_coeffSegment g32p_row32_traceSegment_067 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 384 10 11, g32p_row32_traceSegment_067_0384_0010, g32p_row32_traceSegment_067_0394_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0364_0041 : g32p_coeffSegment g32p_row32_traceSegment_067 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 364 20 21, g32p_row32_traceSegment_067_0364_0020, g32p_row32_traceSegment_067_0384_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0324_0081 : g32p_coeffSegment g32p_row32_traceSegment_067 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 324 40 41, g32p_row32_traceSegment_067_0324_0040, g32p_row32_traceSegment_067_0364_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0405_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 405 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0415_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 415 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0405_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 405 10 10, g32p_row32_traceSegment_067_0405_0010, g32p_row32_traceSegment_067_0415_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0425_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 425 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0435_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 435 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0425_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 425 10 10, g32p_row32_traceSegment_067_0425_0010, g32p_row32_traceSegment_067_0435_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0405_0040 : g32p_coeffSegment g32p_row32_traceSegment_067 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 405 20 20, g32p_row32_traceSegment_067_0405_0020, g32p_row32_traceSegment_067_0425_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0445_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 445 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0455_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 455 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0445_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 445 10 10, g32p_row32_traceSegment_067_0445_0010, g32p_row32_traceSegment_067_0455_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0465_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 465 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0475_0011 : g32p_coeffSegment g32p_row32_traceSegment_067 475 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0465_0021 : g32p_coeffSegment g32p_row32_traceSegment_067 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 465 10 11, g32p_row32_traceSegment_067_0465_0010, g32p_row32_traceSegment_067_0475_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0445_0041 : g32p_coeffSegment g32p_row32_traceSegment_067 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 445 20 21, g32p_row32_traceSegment_067_0445_0020, g32p_row32_traceSegment_067_0465_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0405_0081 : g32p_coeffSegment g32p_row32_traceSegment_067 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 405 40 41, g32p_row32_traceSegment_067_0405_0040, g32p_row32_traceSegment_067_0445_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0324_0162 : g32p_coeffSegment g32p_row32_traceSegment_067 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 324 81 81, g32p_row32_traceSegment_067_0324_0081, g32p_row32_traceSegment_067_0405_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0486_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 486 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0496_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 496 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0486_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 486 10 10, g32p_row32_traceSegment_067_0486_0010, g32p_row32_traceSegment_067_0496_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0506_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 506 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0516_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 516 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0506_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 506 10 10, g32p_row32_traceSegment_067_0506_0010, g32p_row32_traceSegment_067_0516_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0486_0040 : g32p_coeffSegment g32p_row32_traceSegment_067 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 486 20 20, g32p_row32_traceSegment_067_0486_0020, g32p_row32_traceSegment_067_0506_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0526_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 526 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0536_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 536 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0526_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 526 10 10, g32p_row32_traceSegment_067_0526_0010, g32p_row32_traceSegment_067_0536_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0546_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 546 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0556_0011 : g32p_coeffSegment g32p_row32_traceSegment_067 556 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0546_0021 : g32p_coeffSegment g32p_row32_traceSegment_067 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 546 10 11, g32p_row32_traceSegment_067_0546_0010, g32p_row32_traceSegment_067_0556_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0526_0041 : g32p_coeffSegment g32p_row32_traceSegment_067 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 526 20 21, g32p_row32_traceSegment_067_0526_0020, g32p_row32_traceSegment_067_0546_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0486_0081 : g32p_coeffSegment g32p_row32_traceSegment_067 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 486 40 41, g32p_row32_traceSegment_067_0486_0040, g32p_row32_traceSegment_067_0526_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0567_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 567 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0577_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 577 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0567_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 567 10 10, g32p_row32_traceSegment_067_0567_0010, g32p_row32_traceSegment_067_0577_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0587_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 587 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0597_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 597 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0587_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 587 10 10, g32p_row32_traceSegment_067_0587_0010, g32p_row32_traceSegment_067_0597_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0567_0040 : g32p_coeffSegment g32p_row32_traceSegment_067 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 567 20 20, g32p_row32_traceSegment_067_0567_0020, g32p_row32_traceSegment_067_0587_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0607_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 607 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0617_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 617 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0607_0020 : g32p_coeffSegment g32p_row32_traceSegment_067 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 607 10 10, g32p_row32_traceSegment_067_0607_0010, g32p_row32_traceSegment_067_0617_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0627_0010 : g32p_coeffSegment g32p_row32_traceSegment_067 627 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0637_0011 : g32p_coeffSegment g32p_row32_traceSegment_067 637 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_067_0627_0021 : g32p_coeffSegment g32p_row32_traceSegment_067 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 627 10 11, g32p_row32_traceSegment_067_0627_0010, g32p_row32_traceSegment_067_0637_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0607_0041 : g32p_coeffSegment g32p_row32_traceSegment_067 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 607 20 21, g32p_row32_traceSegment_067_0607_0020, g32p_row32_traceSegment_067_0627_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0567_0081 : g32p_coeffSegment g32p_row32_traceSegment_067 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 567 40 41, g32p_row32_traceSegment_067_0567_0040, g32p_row32_traceSegment_067_0607_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0486_0162 : g32p_coeffSegment g32p_row32_traceSegment_067 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 486 81 81, g32p_row32_traceSegment_067_0486_0081, g32p_row32_traceSegment_067_0567_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0324_0324 : g32p_coeffSegment g32p_row32_traceSegment_067 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 324 162 162, g32p_row32_traceSegment_067_0324_0162, g32p_row32_traceSegment_067_0486_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_067_0000_0648 : g32p_coeffSegment g32p_row32_traceSegment_067 0 648 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_067 0 324 324, g32p_row32_traceSegment_067_0000_0324, g32p_row32_traceSegment_067_0324_0324]
  decide +kernel

theorem g32p_row32_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 67 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row32_traceSegment_067_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row32_traceSegment_069 (k : ℕ) : List ℤ :=
  if g32p_row32_supplierClassifier (Fin.ofNat 648 k) = 69 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row32_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row32_traceSegment_069_0000_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 0 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0010_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 10 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0000_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 0 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 0 10 10, g32p_row32_traceSegment_069_0000_0010, g32p_row32_traceSegment_069_0010_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0020_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 20 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0030_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 30 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0020_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 20 10 10, g32p_row32_traceSegment_069_0020_0010, g32p_row32_traceSegment_069_0030_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0000_0040 : g32p_coeffSegment g32p_row32_traceSegment_069 0 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 0 20 20, g32p_row32_traceSegment_069_0000_0020, g32p_row32_traceSegment_069_0020_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0040_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 40 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0050_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 50 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0040_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 40 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 40 10 10, g32p_row32_traceSegment_069_0040_0010, g32p_row32_traceSegment_069_0050_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0060_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 60 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0070_0011 : g32p_coeffSegment g32p_row32_traceSegment_069 70 11 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0060_0021 : g32p_coeffSegment g32p_row32_traceSegment_069 60 21 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 60 10 11, g32p_row32_traceSegment_069_0060_0010, g32p_row32_traceSegment_069_0070_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0040_0041 : g32p_coeffSegment g32p_row32_traceSegment_069 40 41 = [3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 40 20 21, g32p_row32_traceSegment_069_0040_0020, g32p_row32_traceSegment_069_0060_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0000_0081 : g32p_coeffSegment g32p_row32_traceSegment_069 0 81 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 0 40 41, g32p_row32_traceSegment_069_0000_0040, g32p_row32_traceSegment_069_0040_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0081_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 81 10 = [2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0091_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 91 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0081_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 81 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 81 10 10, g32p_row32_traceSegment_069_0081_0010, g32p_row32_traceSegment_069_0091_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0101_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 101 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0111_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 111 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0101_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 101 10 10, g32p_row32_traceSegment_069_0101_0010, g32p_row32_traceSegment_069_0111_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0081_0040 : g32p_coeffSegment g32p_row32_traceSegment_069 81 40 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 81 20 20, g32p_row32_traceSegment_069_0081_0020, g32p_row32_traceSegment_069_0101_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0121_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 121 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0131_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 131 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0121_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 121 10 10, g32p_row32_traceSegment_069_0121_0010, g32p_row32_traceSegment_069_0131_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0141_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 141 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0151_0011 : g32p_coeffSegment g32p_row32_traceSegment_069 151 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0141_0021 : g32p_coeffSegment g32p_row32_traceSegment_069 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 141 10 11, g32p_row32_traceSegment_069_0141_0010, g32p_row32_traceSegment_069_0151_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0121_0041 : g32p_coeffSegment g32p_row32_traceSegment_069 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 121 20 21, g32p_row32_traceSegment_069_0121_0020, g32p_row32_traceSegment_069_0141_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0081_0081 : g32p_coeffSegment g32p_row32_traceSegment_069 81 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 81 40 41, g32p_row32_traceSegment_069_0081_0040, g32p_row32_traceSegment_069_0121_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0000_0162 : g32p_coeffSegment g32p_row32_traceSegment_069 0 162 = [6] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 0 81 81, g32p_row32_traceSegment_069_0000_0081, g32p_row32_traceSegment_069_0081_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0162_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 162 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0172_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 172 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0162_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 162 10 10, g32p_row32_traceSegment_069_0162_0010, g32p_row32_traceSegment_069_0172_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0182_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 182 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0192_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 192 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0182_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 182 10 10, g32p_row32_traceSegment_069_0182_0010, g32p_row32_traceSegment_069_0192_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0162_0040 : g32p_coeffSegment g32p_row32_traceSegment_069 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 162 20 20, g32p_row32_traceSegment_069_0162_0020, g32p_row32_traceSegment_069_0182_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0202_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 202 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0212_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 212 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0202_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 202 10 10, g32p_row32_traceSegment_069_0202_0010, g32p_row32_traceSegment_069_0212_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0222_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 222 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0232_0011 : g32p_coeffSegment g32p_row32_traceSegment_069 232 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0222_0021 : g32p_coeffSegment g32p_row32_traceSegment_069 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 222 10 11, g32p_row32_traceSegment_069_0222_0010, g32p_row32_traceSegment_069_0232_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0202_0041 : g32p_coeffSegment g32p_row32_traceSegment_069 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 202 20 21, g32p_row32_traceSegment_069_0202_0020, g32p_row32_traceSegment_069_0222_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0162_0081 : g32p_coeffSegment g32p_row32_traceSegment_069 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 162 40 41, g32p_row32_traceSegment_069_0162_0040, g32p_row32_traceSegment_069_0202_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0243_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 243 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0253_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 253 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0243_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 243 10 10, g32p_row32_traceSegment_069_0243_0010, g32p_row32_traceSegment_069_0253_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0263_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 263 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0273_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 273 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0263_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 263 10 10, g32p_row32_traceSegment_069_0263_0010, g32p_row32_traceSegment_069_0273_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0243_0040 : g32p_coeffSegment g32p_row32_traceSegment_069 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 243 20 20, g32p_row32_traceSegment_069_0243_0020, g32p_row32_traceSegment_069_0263_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0283_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 283 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0293_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 293 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0283_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 283 10 10, g32p_row32_traceSegment_069_0283_0010, g32p_row32_traceSegment_069_0293_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0303_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 303 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0313_0011 : g32p_coeffSegment g32p_row32_traceSegment_069 313 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0303_0021 : g32p_coeffSegment g32p_row32_traceSegment_069 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 303 10 11, g32p_row32_traceSegment_069_0303_0010, g32p_row32_traceSegment_069_0313_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0283_0041 : g32p_coeffSegment g32p_row32_traceSegment_069 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 283 20 21, g32p_row32_traceSegment_069_0283_0020, g32p_row32_traceSegment_069_0303_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0243_0081 : g32p_coeffSegment g32p_row32_traceSegment_069 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 243 40 41, g32p_row32_traceSegment_069_0243_0040, g32p_row32_traceSegment_069_0283_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0162_0162 : g32p_coeffSegment g32p_row32_traceSegment_069 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 162 81 81, g32p_row32_traceSegment_069_0162_0081, g32p_row32_traceSegment_069_0243_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0000_0324 : g32p_coeffSegment g32p_row32_traceSegment_069 0 324 = [6] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 0 162 162, g32p_row32_traceSegment_069_0000_0162, g32p_row32_traceSegment_069_0162_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0324_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 324 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0334_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 334 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0324_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 324 10 10, g32p_row32_traceSegment_069_0324_0010, g32p_row32_traceSegment_069_0334_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0344_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 344 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0354_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 354 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0344_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 344 10 10, g32p_row32_traceSegment_069_0344_0010, g32p_row32_traceSegment_069_0354_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0324_0040 : g32p_coeffSegment g32p_row32_traceSegment_069 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 324 20 20, g32p_row32_traceSegment_069_0324_0020, g32p_row32_traceSegment_069_0344_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0364_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 364 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0374_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 374 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0364_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 364 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 364 10 10, g32p_row32_traceSegment_069_0364_0010, g32p_row32_traceSegment_069_0374_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0384_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 384 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0394_0011 : g32p_coeffSegment g32p_row32_traceSegment_069 394 11 = [2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0384_0021 : g32p_coeffSegment g32p_row32_traceSegment_069 384 21 = [3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 384 10 11, g32p_row32_traceSegment_069_0384_0010, g32p_row32_traceSegment_069_0394_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0364_0041 : g32p_coeffSegment g32p_row32_traceSegment_069 364 41 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 364 20 21, g32p_row32_traceSegment_069_0364_0020, g32p_row32_traceSegment_069_0384_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0324_0081 : g32p_coeffSegment g32p_row32_traceSegment_069 324 81 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 324 40 41, g32p_row32_traceSegment_069_0324_0040, g32p_row32_traceSegment_069_0364_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0405_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 405 10 = [2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0415_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 415 10 = [2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0405_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 405 20 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 405 10 10, g32p_row32_traceSegment_069_0405_0010, g32p_row32_traceSegment_069_0415_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0425_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 425 10 = [3] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0435_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 435 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0425_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 425 20 = [3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 425 10 10, g32p_row32_traceSegment_069_0425_0010, g32p_row32_traceSegment_069_0435_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0405_0040 : g32p_coeffSegment g32p_row32_traceSegment_069 405 40 = [7] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 405 20 20, g32p_row32_traceSegment_069_0405_0020, g32p_row32_traceSegment_069_0425_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0445_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 445 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0455_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 455 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0445_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 445 10 10, g32p_row32_traceSegment_069_0445_0010, g32p_row32_traceSegment_069_0455_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0465_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 465 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0475_0011 : g32p_coeffSegment g32p_row32_traceSegment_069 475 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0465_0021 : g32p_coeffSegment g32p_row32_traceSegment_069 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 465 10 11, g32p_row32_traceSegment_069_0465_0010, g32p_row32_traceSegment_069_0475_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0445_0041 : g32p_coeffSegment g32p_row32_traceSegment_069 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 445 20 21, g32p_row32_traceSegment_069_0445_0020, g32p_row32_traceSegment_069_0465_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0405_0081 : g32p_coeffSegment g32p_row32_traceSegment_069 405 81 = [7] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 405 40 41, g32p_row32_traceSegment_069_0405_0040, g32p_row32_traceSegment_069_0445_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0324_0162 : g32p_coeffSegment g32p_row32_traceSegment_069 324 162 = [11] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 324 81 81, g32p_row32_traceSegment_069_0324_0081, g32p_row32_traceSegment_069_0405_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0486_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 486 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0496_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 496 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0486_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 486 10 10, g32p_row32_traceSegment_069_0486_0010, g32p_row32_traceSegment_069_0496_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0506_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 506 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0516_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 516 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0506_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 506 10 10, g32p_row32_traceSegment_069_0506_0010, g32p_row32_traceSegment_069_0516_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0486_0040 : g32p_coeffSegment g32p_row32_traceSegment_069 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 486 20 20, g32p_row32_traceSegment_069_0486_0020, g32p_row32_traceSegment_069_0506_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0526_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 526 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0536_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 536 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0526_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 526 10 10, g32p_row32_traceSegment_069_0526_0010, g32p_row32_traceSegment_069_0536_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0546_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 546 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0556_0011 : g32p_coeffSegment g32p_row32_traceSegment_069 556 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0546_0021 : g32p_coeffSegment g32p_row32_traceSegment_069 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 546 10 11, g32p_row32_traceSegment_069_0546_0010, g32p_row32_traceSegment_069_0556_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0526_0041 : g32p_coeffSegment g32p_row32_traceSegment_069 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 526 20 21, g32p_row32_traceSegment_069_0526_0020, g32p_row32_traceSegment_069_0546_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0486_0081 : g32p_coeffSegment g32p_row32_traceSegment_069 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 486 40 41, g32p_row32_traceSegment_069_0486_0040, g32p_row32_traceSegment_069_0526_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0567_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 567 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0577_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 577 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0567_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 567 10 10, g32p_row32_traceSegment_069_0567_0010, g32p_row32_traceSegment_069_0577_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0587_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 587 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0597_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 597 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0587_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 587 10 10, g32p_row32_traceSegment_069_0587_0010, g32p_row32_traceSegment_069_0597_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0567_0040 : g32p_coeffSegment g32p_row32_traceSegment_069 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 567 20 20, g32p_row32_traceSegment_069_0567_0020, g32p_row32_traceSegment_069_0587_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0607_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 607 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0617_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 617 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0607_0020 : g32p_coeffSegment g32p_row32_traceSegment_069 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 607 10 10, g32p_row32_traceSegment_069_0607_0010, g32p_row32_traceSegment_069_0617_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0627_0010 : g32p_coeffSegment g32p_row32_traceSegment_069 627 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0637_0011 : g32p_coeffSegment g32p_row32_traceSegment_069 637 11 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_069_0627_0021 : g32p_coeffSegment g32p_row32_traceSegment_069 627 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 627 10 11, g32p_row32_traceSegment_069_0627_0010, g32p_row32_traceSegment_069_0637_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0607_0041 : g32p_coeffSegment g32p_row32_traceSegment_069 607 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 607 20 21, g32p_row32_traceSegment_069_0607_0020, g32p_row32_traceSegment_069_0627_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0567_0081 : g32p_coeffSegment g32p_row32_traceSegment_069 567 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 567 40 41, g32p_row32_traceSegment_069_0567_0040, g32p_row32_traceSegment_069_0607_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0486_0162 : g32p_coeffSegment g32p_row32_traceSegment_069 486 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 486 81 81, g32p_row32_traceSegment_069_0486_0081, g32p_row32_traceSegment_069_0567_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0324_0324 : g32p_coeffSegment g32p_row32_traceSegment_069 324 324 = [12] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 324 162 162, g32p_row32_traceSegment_069_0324_0162, g32p_row32_traceSegment_069_0486_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_069_0000_0648 : g32p_coeffSegment g32p_row32_traceSegment_069 0 648 = [18] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_069 0 324 324, g32p_row32_traceSegment_069_0000_0324, g32p_row32_traceSegment_069_0324_0324]
  decide +kernel

theorem g32p_row32_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 69 = [18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row32_traceSegment_069_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row32_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 44) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 44) (g32p_literalTraceValue 31 44)
      [1, 1, 1] [] = true := by
  rw [g32p_row32_traceCoefficients_044]
  decide +kernel

theorem g32p_row32_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 45) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 45) (g32p_literalTraceValue 31 45)
      [1, 1, 1] [] = true := by
  rw [g32p_row32_traceCoefficients_045]
  decide +kernel

theorem g32p_row32_tracePolynomial_046 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 46) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 46) (g32p_literalTraceValue 31 46)
      [1, 1, 1] [] = true := by
  rw [g32p_row32_traceCoefficients_046]
  decide +kernel

theorem g32p_row32_tracePolynomial_049 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 49) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 49) (g32p_literalTraceValue 31 49)
      [1, 1, 1] [] = true := by
  rw [g32p_row32_traceCoefficients_049]
  decide +kernel

theorem g32p_row32_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 56) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 56) (g32p_literalTraceValue 31 56)
      [1, 1, 1] [] = true := by
  rw [g32p_row32_traceCoefficients_056]
  decide +kernel

theorem g32p_row32_tracePolynomial_057 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 57) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 57) (g32p_literalTraceValue 31 57)
      [1, 1, 1] [2592] = true := by
  rw [g32p_row32_traceCoefficients_057]
  decide +kernel

theorem g32p_row32_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 67) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 67) (g32p_literalTraceValue 31 67)
      [1, 1, 1] [] = true := by
  rw [g32p_row32_traceCoefficients_067]
  decide +kernel

theorem g32p_row32_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer 69) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 69) (g32p_literalTraceValue 31 69)
      [1, 1, 1] [] = true := by
  rw [g32p_row32_traceCoefficients_069]
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

private def g32p_row32_traceSegment_075 (k : ℕ) : List ℤ :=
  if g32p_row32_supplierClassifier (Fin.ofNat 648 k) = 75 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row32_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row32_traceSegment_075_0000_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 0 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0010_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 10 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0000_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 0 10 10, g32p_row32_traceSegment_075_0000_0010, g32p_row32_traceSegment_075_0010_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0020_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 20 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0030_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 30 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0020_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 20 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 20 10 10, g32p_row32_traceSegment_075_0020_0010, g32p_row32_traceSegment_075_0030_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0000_0040 : g32p_coeffSegment g32p_row32_traceSegment_075 0 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 0 20 20, g32p_row32_traceSegment_075_0000_0020, g32p_row32_traceSegment_075_0020_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0040_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 40 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0050_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 50 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0040_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 40 10 10, g32p_row32_traceSegment_075_0040_0010, g32p_row32_traceSegment_075_0050_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0060_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 60 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0070_0011 : g32p_coeffSegment g32p_row32_traceSegment_075 70 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0060_0021 : g32p_coeffSegment g32p_row32_traceSegment_075 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 60 10 11, g32p_row32_traceSegment_075_0060_0010, g32p_row32_traceSegment_075_0070_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0040_0041 : g32p_coeffSegment g32p_row32_traceSegment_075 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 40 20 21, g32p_row32_traceSegment_075_0040_0020, g32p_row32_traceSegment_075_0060_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0000_0081 : g32p_coeffSegment g32p_row32_traceSegment_075 0 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 0 40 41, g32p_row32_traceSegment_075_0000_0040, g32p_row32_traceSegment_075_0040_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0081_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 81 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0091_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 91 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0081_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 81 10 10, g32p_row32_traceSegment_075_0081_0010, g32p_row32_traceSegment_075_0091_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0101_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 101 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0111_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 111 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0101_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 101 10 10, g32p_row32_traceSegment_075_0101_0010, g32p_row32_traceSegment_075_0111_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0081_0040 : g32p_coeffSegment g32p_row32_traceSegment_075 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 81 20 20, g32p_row32_traceSegment_075_0081_0020, g32p_row32_traceSegment_075_0101_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0121_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 121 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0131_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 131 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0121_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 121 10 10, g32p_row32_traceSegment_075_0121_0010, g32p_row32_traceSegment_075_0131_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0141_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 141 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0151_0011 : g32p_coeffSegment g32p_row32_traceSegment_075 151 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0141_0021 : g32p_coeffSegment g32p_row32_traceSegment_075 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 141 10 11, g32p_row32_traceSegment_075_0141_0010, g32p_row32_traceSegment_075_0151_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0121_0041 : g32p_coeffSegment g32p_row32_traceSegment_075 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 121 20 21, g32p_row32_traceSegment_075_0121_0020, g32p_row32_traceSegment_075_0141_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0081_0081 : g32p_coeffSegment g32p_row32_traceSegment_075 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 81 40 41, g32p_row32_traceSegment_075_0081_0040, g32p_row32_traceSegment_075_0121_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0000_0162 : g32p_coeffSegment g32p_row32_traceSegment_075 0 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 0 81 81, g32p_row32_traceSegment_075_0000_0081, g32p_row32_traceSegment_075_0081_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0162_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 162 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0172_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 172 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0162_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 162 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 162 10 10, g32p_row32_traceSegment_075_0162_0010, g32p_row32_traceSegment_075_0172_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0182_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 182 10 = [2] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0192_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 192 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0182_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 182 20 = [3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 182 10 10, g32p_row32_traceSegment_075_0182_0010, g32p_row32_traceSegment_075_0192_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0162_0040 : g32p_coeffSegment g32p_row32_traceSegment_075 162 40 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 162 20 20, g32p_row32_traceSegment_075_0162_0020, g32p_row32_traceSegment_075_0182_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0202_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 202 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0212_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 212 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0202_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 202 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 202 10 10, g32p_row32_traceSegment_075_0202_0010, g32p_row32_traceSegment_075_0212_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0222_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 222 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0232_0011 : g32p_coeffSegment g32p_row32_traceSegment_075 232 11 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0222_0021 : g32p_coeffSegment g32p_row32_traceSegment_075 222 21 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 222 10 11, g32p_row32_traceSegment_075_0222_0010, g32p_row32_traceSegment_075_0232_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0202_0041 : g32p_coeffSegment g32p_row32_traceSegment_075 202 41 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 202 20 21, g32p_row32_traceSegment_075_0202_0020, g32p_row32_traceSegment_075_0222_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0162_0081 : g32p_coeffSegment g32p_row32_traceSegment_075 162 81 = [8] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 162 40 41, g32p_row32_traceSegment_075_0162_0040, g32p_row32_traceSegment_075_0202_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0243_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 243 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0253_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 253 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0243_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 243 10 10, g32p_row32_traceSegment_075_0243_0010, g32p_row32_traceSegment_075_0253_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0263_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 263 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0273_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 273 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0263_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 263 10 10, g32p_row32_traceSegment_075_0263_0010, g32p_row32_traceSegment_075_0273_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0243_0040 : g32p_coeffSegment g32p_row32_traceSegment_075 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 243 20 20, g32p_row32_traceSegment_075_0243_0020, g32p_row32_traceSegment_075_0263_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0283_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 283 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0293_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 293 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0283_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 283 10 10, g32p_row32_traceSegment_075_0283_0010, g32p_row32_traceSegment_075_0293_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0303_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 303 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0313_0011 : g32p_coeffSegment g32p_row32_traceSegment_075 313 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0303_0021 : g32p_coeffSegment g32p_row32_traceSegment_075 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 303 10 11, g32p_row32_traceSegment_075_0303_0010, g32p_row32_traceSegment_075_0313_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0283_0041 : g32p_coeffSegment g32p_row32_traceSegment_075 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 283 20 21, g32p_row32_traceSegment_075_0283_0020, g32p_row32_traceSegment_075_0303_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0243_0081 : g32p_coeffSegment g32p_row32_traceSegment_075 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 243 40 41, g32p_row32_traceSegment_075_0243_0040, g32p_row32_traceSegment_075_0283_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0162_0162 : g32p_coeffSegment g32p_row32_traceSegment_075 162 162 = [8] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 162 81 81, g32p_row32_traceSegment_075_0162_0081, g32p_row32_traceSegment_075_0243_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0000_0324 : g32p_coeffSegment g32p_row32_traceSegment_075 0 324 = [9] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 0 162 162, g32p_row32_traceSegment_075_0000_0162, g32p_row32_traceSegment_075_0162_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0324_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 324 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0334_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 334 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0324_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 324 10 10, g32p_row32_traceSegment_075_0324_0010, g32p_row32_traceSegment_075_0334_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0344_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 344 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0354_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 354 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0344_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 344 10 10, g32p_row32_traceSegment_075_0344_0010, g32p_row32_traceSegment_075_0354_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0324_0040 : g32p_coeffSegment g32p_row32_traceSegment_075 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 324 20 20, g32p_row32_traceSegment_075_0324_0020, g32p_row32_traceSegment_075_0344_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0364_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 364 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0374_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 374 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0364_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 364 10 10, g32p_row32_traceSegment_075_0364_0010, g32p_row32_traceSegment_075_0374_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0384_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 384 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0394_0011 : g32p_coeffSegment g32p_row32_traceSegment_075 394 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0384_0021 : g32p_coeffSegment g32p_row32_traceSegment_075 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 384 10 11, g32p_row32_traceSegment_075_0384_0010, g32p_row32_traceSegment_075_0394_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0364_0041 : g32p_coeffSegment g32p_row32_traceSegment_075 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 364 20 21, g32p_row32_traceSegment_075_0364_0020, g32p_row32_traceSegment_075_0384_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0324_0081 : g32p_coeffSegment g32p_row32_traceSegment_075 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 324 40 41, g32p_row32_traceSegment_075_0324_0040, g32p_row32_traceSegment_075_0364_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0405_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 405 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0415_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 415 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0405_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 405 10 10, g32p_row32_traceSegment_075_0405_0010, g32p_row32_traceSegment_075_0415_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0425_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 425 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0435_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 435 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0425_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 425 10 10, g32p_row32_traceSegment_075_0425_0010, g32p_row32_traceSegment_075_0435_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0405_0040 : g32p_coeffSegment g32p_row32_traceSegment_075 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 405 20 20, g32p_row32_traceSegment_075_0405_0020, g32p_row32_traceSegment_075_0425_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0445_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 445 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0455_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 455 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0445_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 445 10 10, g32p_row32_traceSegment_075_0445_0010, g32p_row32_traceSegment_075_0455_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0465_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 465 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0475_0011 : g32p_coeffSegment g32p_row32_traceSegment_075 475 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0465_0021 : g32p_coeffSegment g32p_row32_traceSegment_075 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 465 10 11, g32p_row32_traceSegment_075_0465_0010, g32p_row32_traceSegment_075_0475_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0445_0041 : g32p_coeffSegment g32p_row32_traceSegment_075 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 445 20 21, g32p_row32_traceSegment_075_0445_0020, g32p_row32_traceSegment_075_0465_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0405_0081 : g32p_coeffSegment g32p_row32_traceSegment_075 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 405 40 41, g32p_row32_traceSegment_075_0405_0040, g32p_row32_traceSegment_075_0445_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0324_0162 : g32p_coeffSegment g32p_row32_traceSegment_075 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 324 81 81, g32p_row32_traceSegment_075_0324_0081, g32p_row32_traceSegment_075_0405_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0486_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 486 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0496_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 496 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0486_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 486 10 10, g32p_row32_traceSegment_075_0486_0010, g32p_row32_traceSegment_075_0496_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0506_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 506 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0516_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 516 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0506_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 506 10 10, g32p_row32_traceSegment_075_0506_0010, g32p_row32_traceSegment_075_0516_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0486_0040 : g32p_coeffSegment g32p_row32_traceSegment_075 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 486 20 20, g32p_row32_traceSegment_075_0486_0020, g32p_row32_traceSegment_075_0506_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0526_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 526 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0536_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 536 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0526_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 526 10 10, g32p_row32_traceSegment_075_0526_0010, g32p_row32_traceSegment_075_0536_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0546_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 546 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0556_0011 : g32p_coeffSegment g32p_row32_traceSegment_075 556 11 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0546_0021 : g32p_coeffSegment g32p_row32_traceSegment_075 546 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 546 10 11, g32p_row32_traceSegment_075_0546_0010, g32p_row32_traceSegment_075_0556_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0526_0041 : g32p_coeffSegment g32p_row32_traceSegment_075 526 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 526 20 21, g32p_row32_traceSegment_075_0526_0020, g32p_row32_traceSegment_075_0546_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0486_0081 : g32p_coeffSegment g32p_row32_traceSegment_075 486 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 486 40 41, g32p_row32_traceSegment_075_0486_0040, g32p_row32_traceSegment_075_0526_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0567_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 567 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0577_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 577 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0567_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 567 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 567 10 10, g32p_row32_traceSegment_075_0567_0010, g32p_row32_traceSegment_075_0577_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0587_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 587 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0597_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 597 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0587_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 587 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 587 10 10, g32p_row32_traceSegment_075_0587_0010, g32p_row32_traceSegment_075_0597_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0567_0040 : g32p_coeffSegment g32p_row32_traceSegment_075 567 40 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 567 20 20, g32p_row32_traceSegment_075_0567_0020, g32p_row32_traceSegment_075_0587_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0607_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 607 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0617_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 617 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0607_0020 : g32p_coeffSegment g32p_row32_traceSegment_075 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 607 10 10, g32p_row32_traceSegment_075_0607_0010, g32p_row32_traceSegment_075_0617_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0627_0010 : g32p_coeffSegment g32p_row32_traceSegment_075 627 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0637_0011 : g32p_coeffSegment g32p_row32_traceSegment_075 637 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_075_0627_0021 : g32p_coeffSegment g32p_row32_traceSegment_075 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 627 10 11, g32p_row32_traceSegment_075_0627_0010, g32p_row32_traceSegment_075_0637_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0607_0041 : g32p_coeffSegment g32p_row32_traceSegment_075 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 607 20 21, g32p_row32_traceSegment_075_0607_0020, g32p_row32_traceSegment_075_0627_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0567_0081 : g32p_coeffSegment g32p_row32_traceSegment_075 567 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 567 40 41, g32p_row32_traceSegment_075_0567_0040, g32p_row32_traceSegment_075_0607_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0486_0162 : g32p_coeffSegment g32p_row32_traceSegment_075 486 162 = [3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 486 81 81, g32p_row32_traceSegment_075_0486_0081, g32p_row32_traceSegment_075_0567_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0324_0324 : g32p_coeffSegment g32p_row32_traceSegment_075 324 324 = [3] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 324 162 162, g32p_row32_traceSegment_075_0324_0162, g32p_row32_traceSegment_075_0486_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_075_0000_0648 : g32p_coeffSegment g32p_row32_traceSegment_075 0 648 = [12] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_075 0 324 324, g32p_row32_traceSegment_075_0000_0324, g32p_row32_traceSegment_075_0324_0324]
  decide +kernel

theorem g32p_row32_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 75 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row32_traceSegment_075_0000_0648

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row32_traceSegment_076 (k : ℕ) : List ℤ :=
  if g32p_row32_supplierClassifier (Fin.ofNat 648 k) = 76 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row32_characterValues (Fin.ofNat 648 k))).val 1 else []

private theorem g32p_row32_traceSegment_076_0000_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 0 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0010_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 10 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0000_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 0 10 10, g32p_row32_traceSegment_076_0000_0010, g32p_row32_traceSegment_076_0010_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0020_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 20 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0030_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 30 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0020_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 20 10 10, g32p_row32_traceSegment_076_0020_0010, g32p_row32_traceSegment_076_0030_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0000_0040 : g32p_coeffSegment g32p_row32_traceSegment_076 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 0 20 20, g32p_row32_traceSegment_076_0000_0020, g32p_row32_traceSegment_076_0020_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0040_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 40 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0050_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 50 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0040_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 40 10 10, g32p_row32_traceSegment_076_0040_0010, g32p_row32_traceSegment_076_0050_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0060_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 60 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0070_0011 : g32p_coeffSegment g32p_row32_traceSegment_076 70 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0060_0021 : g32p_coeffSegment g32p_row32_traceSegment_076 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 60 10 11, g32p_row32_traceSegment_076_0060_0010, g32p_row32_traceSegment_076_0070_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0040_0041 : g32p_coeffSegment g32p_row32_traceSegment_076 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 40 20 21, g32p_row32_traceSegment_076_0040_0020, g32p_row32_traceSegment_076_0060_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0000_0081 : g32p_coeffSegment g32p_row32_traceSegment_076 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 0 40 41, g32p_row32_traceSegment_076_0000_0040, g32p_row32_traceSegment_076_0040_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0081_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 81 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0091_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 91 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0081_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 81 10 10, g32p_row32_traceSegment_076_0081_0010, g32p_row32_traceSegment_076_0091_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0101_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 101 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0111_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 111 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0101_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 101 10 10, g32p_row32_traceSegment_076_0101_0010, g32p_row32_traceSegment_076_0111_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0081_0040 : g32p_coeffSegment g32p_row32_traceSegment_076 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 81 20 20, g32p_row32_traceSegment_076_0081_0020, g32p_row32_traceSegment_076_0101_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0121_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 121 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0131_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 131 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0121_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 121 10 10, g32p_row32_traceSegment_076_0121_0010, g32p_row32_traceSegment_076_0131_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0141_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 141 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0151_0011 : g32p_coeffSegment g32p_row32_traceSegment_076 151 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0141_0021 : g32p_coeffSegment g32p_row32_traceSegment_076 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 141 10 11, g32p_row32_traceSegment_076_0141_0010, g32p_row32_traceSegment_076_0151_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0121_0041 : g32p_coeffSegment g32p_row32_traceSegment_076 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 121 20 21, g32p_row32_traceSegment_076_0121_0020, g32p_row32_traceSegment_076_0141_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0081_0081 : g32p_coeffSegment g32p_row32_traceSegment_076 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 81 40 41, g32p_row32_traceSegment_076_0081_0040, g32p_row32_traceSegment_076_0121_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0000_0162 : g32p_coeffSegment g32p_row32_traceSegment_076 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 0 81 81, g32p_row32_traceSegment_076_0000_0081, g32p_row32_traceSegment_076_0081_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0162_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 162 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0172_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 172 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0162_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 162 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 162 10 10, g32p_row32_traceSegment_076_0162_0010, g32p_row32_traceSegment_076_0172_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0182_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 182 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0192_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 192 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0182_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 182 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 182 10 10, g32p_row32_traceSegment_076_0182_0010, g32p_row32_traceSegment_076_0192_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0162_0040 : g32p_coeffSegment g32p_row32_traceSegment_076 162 40 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 162 20 20, g32p_row32_traceSegment_076_0162_0020, g32p_row32_traceSegment_076_0182_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0202_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 202 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0212_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 212 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0202_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 202 10 10, g32p_row32_traceSegment_076_0202_0010, g32p_row32_traceSegment_076_0212_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0222_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 222 10 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0232_0011 : g32p_coeffSegment g32p_row32_traceSegment_076 232 11 = [1] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0222_0021 : g32p_coeffSegment g32p_row32_traceSegment_076 222 21 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 222 10 11, g32p_row32_traceSegment_076_0222_0010, g32p_row32_traceSegment_076_0232_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0202_0041 : g32p_coeffSegment g32p_row32_traceSegment_076 202 41 = [2] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 202 20 21, g32p_row32_traceSegment_076_0202_0020, g32p_row32_traceSegment_076_0222_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0162_0081 : g32p_coeffSegment g32p_row32_traceSegment_076 162 81 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 162 40 41, g32p_row32_traceSegment_076_0162_0040, g32p_row32_traceSegment_076_0202_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0243_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 243 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0253_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 253 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0243_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 243 10 10, g32p_row32_traceSegment_076_0243_0010, g32p_row32_traceSegment_076_0253_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0263_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 263 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0273_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 273 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0263_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 263 10 10, g32p_row32_traceSegment_076_0263_0010, g32p_row32_traceSegment_076_0273_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0243_0040 : g32p_coeffSegment g32p_row32_traceSegment_076 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 243 20 20, g32p_row32_traceSegment_076_0243_0020, g32p_row32_traceSegment_076_0263_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0283_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 283 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0293_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 293 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0283_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 283 10 10, g32p_row32_traceSegment_076_0283_0010, g32p_row32_traceSegment_076_0293_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0303_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 303 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0313_0011 : g32p_coeffSegment g32p_row32_traceSegment_076 313 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0303_0021 : g32p_coeffSegment g32p_row32_traceSegment_076 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 303 10 11, g32p_row32_traceSegment_076_0303_0010, g32p_row32_traceSegment_076_0313_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0283_0041 : g32p_coeffSegment g32p_row32_traceSegment_076 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 283 20 21, g32p_row32_traceSegment_076_0283_0020, g32p_row32_traceSegment_076_0303_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0243_0081 : g32p_coeffSegment g32p_row32_traceSegment_076 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 243 40 41, g32p_row32_traceSegment_076_0243_0040, g32p_row32_traceSegment_076_0283_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0162_0162 : g32p_coeffSegment g32p_row32_traceSegment_076 162 162 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 162 81 81, g32p_row32_traceSegment_076_0162_0081, g32p_row32_traceSegment_076_0243_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0000_0324 : g32p_coeffSegment g32p_row32_traceSegment_076 0 324 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 0 162 162, g32p_row32_traceSegment_076_0000_0162, g32p_row32_traceSegment_076_0162_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0324_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 324 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0334_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 334 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0324_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 324 10 10, g32p_row32_traceSegment_076_0324_0010, g32p_row32_traceSegment_076_0334_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0344_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 344 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0354_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 354 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0344_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 344 10 10, g32p_row32_traceSegment_076_0344_0010, g32p_row32_traceSegment_076_0354_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0324_0040 : g32p_coeffSegment g32p_row32_traceSegment_076 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 324 20 20, g32p_row32_traceSegment_076_0324_0020, g32p_row32_traceSegment_076_0344_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0364_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 364 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0374_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 374 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0364_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 364 10 10, g32p_row32_traceSegment_076_0364_0010, g32p_row32_traceSegment_076_0374_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0384_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 384 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0394_0011 : g32p_coeffSegment g32p_row32_traceSegment_076 394 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0384_0021 : g32p_coeffSegment g32p_row32_traceSegment_076 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 384 10 11, g32p_row32_traceSegment_076_0384_0010, g32p_row32_traceSegment_076_0394_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0364_0041 : g32p_coeffSegment g32p_row32_traceSegment_076 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 364 20 21, g32p_row32_traceSegment_076_0364_0020, g32p_row32_traceSegment_076_0384_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0324_0081 : g32p_coeffSegment g32p_row32_traceSegment_076 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 324 40 41, g32p_row32_traceSegment_076_0324_0040, g32p_row32_traceSegment_076_0364_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0405_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 405 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0415_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 415 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0405_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 405 10 10, g32p_row32_traceSegment_076_0405_0010, g32p_row32_traceSegment_076_0415_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0425_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 425 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0435_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 435 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0425_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 425 10 10, g32p_row32_traceSegment_076_0425_0010, g32p_row32_traceSegment_076_0435_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0405_0040 : g32p_coeffSegment g32p_row32_traceSegment_076 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 405 20 20, g32p_row32_traceSegment_076_0405_0020, g32p_row32_traceSegment_076_0425_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0445_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 445 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0455_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 455 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0445_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 445 10 10, g32p_row32_traceSegment_076_0445_0010, g32p_row32_traceSegment_076_0455_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0465_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 465 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0475_0011 : g32p_coeffSegment g32p_row32_traceSegment_076 475 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0465_0021 : g32p_coeffSegment g32p_row32_traceSegment_076 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 465 10 11, g32p_row32_traceSegment_076_0465_0010, g32p_row32_traceSegment_076_0475_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0445_0041 : g32p_coeffSegment g32p_row32_traceSegment_076 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 445 20 21, g32p_row32_traceSegment_076_0445_0020, g32p_row32_traceSegment_076_0465_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0405_0081 : g32p_coeffSegment g32p_row32_traceSegment_076 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 405 40 41, g32p_row32_traceSegment_076_0405_0040, g32p_row32_traceSegment_076_0445_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0324_0162 : g32p_coeffSegment g32p_row32_traceSegment_076 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 324 81 81, g32p_row32_traceSegment_076_0324_0081, g32p_row32_traceSegment_076_0405_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0486_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 486 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0496_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 496 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0486_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 486 10 10, g32p_row32_traceSegment_076_0486_0010, g32p_row32_traceSegment_076_0496_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0506_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 506 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0516_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 516 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0506_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 506 10 10, g32p_row32_traceSegment_076_0506_0010, g32p_row32_traceSegment_076_0516_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0486_0040 : g32p_coeffSegment g32p_row32_traceSegment_076 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 486 20 20, g32p_row32_traceSegment_076_0486_0020, g32p_row32_traceSegment_076_0506_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0526_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 526 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0536_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 536 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0526_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 526 10 10, g32p_row32_traceSegment_076_0526_0010, g32p_row32_traceSegment_076_0536_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0546_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 546 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0556_0011 : g32p_coeffSegment g32p_row32_traceSegment_076 556 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0546_0021 : g32p_coeffSegment g32p_row32_traceSegment_076 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 546 10 11, g32p_row32_traceSegment_076_0546_0010, g32p_row32_traceSegment_076_0556_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0526_0041 : g32p_coeffSegment g32p_row32_traceSegment_076 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 526 20 21, g32p_row32_traceSegment_076_0526_0020, g32p_row32_traceSegment_076_0546_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0486_0081 : g32p_coeffSegment g32p_row32_traceSegment_076 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 486 40 41, g32p_row32_traceSegment_076_0486_0040, g32p_row32_traceSegment_076_0526_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0567_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 567 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0577_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 577 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0567_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 567 10 10, g32p_row32_traceSegment_076_0567_0010, g32p_row32_traceSegment_076_0577_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0587_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 587 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0597_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 597 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0587_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 587 10 10, g32p_row32_traceSegment_076_0587_0010, g32p_row32_traceSegment_076_0597_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0567_0040 : g32p_coeffSegment g32p_row32_traceSegment_076 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 567 20 20, g32p_row32_traceSegment_076_0567_0020, g32p_row32_traceSegment_076_0587_0020]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0607_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 607 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0617_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 617 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0607_0020 : g32p_coeffSegment g32p_row32_traceSegment_076 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 607 10 10, g32p_row32_traceSegment_076_0607_0010, g32p_row32_traceSegment_076_0617_0010]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0627_0010 : g32p_coeffSegment g32p_row32_traceSegment_076 627 10 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0637_0011 : g32p_coeffSegment g32p_row32_traceSegment_076 637 11 = [] := by
  decide +kernel

private theorem g32p_row32_traceSegment_076_0627_0021 : g32p_coeffSegment g32p_row32_traceSegment_076 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 627 10 11, g32p_row32_traceSegment_076_0627_0010, g32p_row32_traceSegment_076_0637_0011]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0607_0041 : g32p_coeffSegment g32p_row32_traceSegment_076 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 607 20 21, g32p_row32_traceSegment_076_0607_0020, g32p_row32_traceSegment_076_0627_0021]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0567_0081 : g32p_coeffSegment g32p_row32_traceSegment_076 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 567 40 41, g32p_row32_traceSegment_076_0567_0040, g32p_row32_traceSegment_076_0607_0041]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0486_0162 : g32p_coeffSegment g32p_row32_traceSegment_076 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 486 81 81, g32p_row32_traceSegment_076_0486_0081, g32p_row32_traceSegment_076_0567_0081]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0324_0324 : g32p_coeffSegment g32p_row32_traceSegment_076 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 324 162 162, g32p_row32_traceSegment_076_0324_0162, g32p_row32_traceSegment_076_0486_0162]
  decide +kernel

private theorem g32p_row32_traceSegment_076_0000_0648 : g32p_coeffSegment g32p_row32_traceSegment_076 0 648 = [4] := by
  rw [g32p_coeffSegment_add g32p_row32_traceSegment_076 0 324 324, g32p_row32_traceSegment_076_0000_0324, g32p_row32_traceSegment_076_0324_0324]
  decide +kernel

theorem g32p_row32_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) 76 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row32_traceSegment_076_0000_0648

end HodgeLean.Foundations.Program

end
end
