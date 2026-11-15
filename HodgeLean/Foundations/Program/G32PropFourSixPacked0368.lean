import HodgeLean.Foundations.Program.G32PropFourSixPacked0367
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_008 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 8 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_008_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 0 10 10, g32p_row17_traceSegment_008_0000_0010, g32p_row17_traceSegment_008_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 20 10 10, g32p_row17_traceSegment_008_0020_0010, g32p_row17_traceSegment_008_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 0 20 20, g32p_row17_traceSegment_008_0000_0020, g32p_row17_traceSegment_008_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 40 10 10, g32p_row17_traceSegment_008_0040_0010, g32p_row17_traceSegment_008_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 60 10 11, g32p_row17_traceSegment_008_0060_0010, g32p_row17_traceSegment_008_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 40 20 21, g32p_row17_traceSegment_008_0040_0020, g32p_row17_traceSegment_008_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 0 40 41, g32p_row17_traceSegment_008_0000_0040, g32p_row17_traceSegment_008_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 81 10 10, g32p_row17_traceSegment_008_0081_0010, g32p_row17_traceSegment_008_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 101 10 10, g32p_row17_traceSegment_008_0101_0010, g32p_row17_traceSegment_008_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 81 20 20, g32p_row17_traceSegment_008_0081_0020, g32p_row17_traceSegment_008_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 121 10 10, g32p_row17_traceSegment_008_0121_0010, g32p_row17_traceSegment_008_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 141 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 141 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 141 10 11, g32p_row17_traceSegment_008_0141_0010, g32p_row17_traceSegment_008_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 121 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 121 20 21, g32p_row17_traceSegment_008_0121_0020, g32p_row17_traceSegment_008_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 81 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 81 40 41, g32p_row17_traceSegment_008_0081_0040, g32p_row17_traceSegment_008_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_008 0 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 0 81 81, g32p_row17_traceSegment_008_0000_0081, g32p_row17_traceSegment_008_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 162 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 162 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 162 10 10, g32p_row17_traceSegment_008_0162_0010, g32p_row17_traceSegment_008_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 182 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 182 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 182 10 10, g32p_row17_traceSegment_008_0182_0010, g32p_row17_traceSegment_008_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 162 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 162 20 20, g32p_row17_traceSegment_008_0162_0020, g32p_row17_traceSegment_008_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 202 10 10, g32p_row17_traceSegment_008_0202_0010, g32p_row17_traceSegment_008_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 222 10 11, g32p_row17_traceSegment_008_0222_0010, g32p_row17_traceSegment_008_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 202 20 21, g32p_row17_traceSegment_008_0202_0020, g32p_row17_traceSegment_008_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 162 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 162 40 41, g32p_row17_traceSegment_008_0162_0040, g32p_row17_traceSegment_008_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 243 10 10, g32p_row17_traceSegment_008_0243_0010, g32p_row17_traceSegment_008_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 263 10 10, g32p_row17_traceSegment_008_0263_0010, g32p_row17_traceSegment_008_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 243 20 20, g32p_row17_traceSegment_008_0243_0020, g32p_row17_traceSegment_008_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 283 10 10, g32p_row17_traceSegment_008_0283_0010, g32p_row17_traceSegment_008_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 303 10 11, g32p_row17_traceSegment_008_0303_0010, g32p_row17_traceSegment_008_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 283 20 21, g32p_row17_traceSegment_008_0283_0020, g32p_row17_traceSegment_008_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 243 40 41, g32p_row17_traceSegment_008_0243_0040, g32p_row17_traceSegment_008_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_008 162 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 162 81 81, g32p_row17_traceSegment_008_0162_0081, g32p_row17_traceSegment_008_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_008 0 324 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 0 162 162, g32p_row17_traceSegment_008_0000_0162, g32p_row17_traceSegment_008_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 324 10 10, g32p_row17_traceSegment_008_0324_0010, g32p_row17_traceSegment_008_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 344 10 10, g32p_row17_traceSegment_008_0344_0010, g32p_row17_traceSegment_008_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 324 20 20, g32p_row17_traceSegment_008_0324_0020, g32p_row17_traceSegment_008_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 364 10 10, g32p_row17_traceSegment_008_0364_0010, g32p_row17_traceSegment_008_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 384 10 11, g32p_row17_traceSegment_008_0384_0010, g32p_row17_traceSegment_008_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 364 20 21, g32p_row17_traceSegment_008_0364_0020, g32p_row17_traceSegment_008_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 324 40 41, g32p_row17_traceSegment_008_0324_0040, g32p_row17_traceSegment_008_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 405 10 10, g32p_row17_traceSegment_008_0405_0010, g32p_row17_traceSegment_008_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 425 10 10, g32p_row17_traceSegment_008_0425_0010, g32p_row17_traceSegment_008_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 405 20 20, g32p_row17_traceSegment_008_0405_0020, g32p_row17_traceSegment_008_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 445 10 10, g32p_row17_traceSegment_008_0445_0010, g32p_row17_traceSegment_008_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 465 10 11, g32p_row17_traceSegment_008_0465_0010, g32p_row17_traceSegment_008_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 445 20 21, g32p_row17_traceSegment_008_0445_0020, g32p_row17_traceSegment_008_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 405 40 41, g32p_row17_traceSegment_008_0405_0040, g32p_row17_traceSegment_008_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_008 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 324 81 81, g32p_row17_traceSegment_008_0324_0081, g32p_row17_traceSegment_008_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 486 10 10, g32p_row17_traceSegment_008_0486_0010, g32p_row17_traceSegment_008_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 506 10 10, g32p_row17_traceSegment_008_0506_0010, g32p_row17_traceSegment_008_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 486 20 20, g32p_row17_traceSegment_008_0486_0020, g32p_row17_traceSegment_008_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 526 10 10, g32p_row17_traceSegment_008_0526_0010, g32p_row17_traceSegment_008_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 546 10 11, g32p_row17_traceSegment_008_0546_0010, g32p_row17_traceSegment_008_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 526 20 21, g32p_row17_traceSegment_008_0526_0020, g32p_row17_traceSegment_008_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 486 40 41, g32p_row17_traceSegment_008_0486_0040, g32p_row17_traceSegment_008_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 567 10 10, g32p_row17_traceSegment_008_0567_0010, g32p_row17_traceSegment_008_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 587 10 10, g32p_row17_traceSegment_008_0587_0010, g32p_row17_traceSegment_008_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 567 20 20, g32p_row17_traceSegment_008_0567_0020, g32p_row17_traceSegment_008_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 607 10 10, g32p_row17_traceSegment_008_0607_0010, g32p_row17_traceSegment_008_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 627 10 11, g32p_row17_traceSegment_008_0627_0010, g32p_row17_traceSegment_008_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 607 20 21, g32p_row17_traceSegment_008_0607_0020, g32p_row17_traceSegment_008_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 567 40 41, g32p_row17_traceSegment_008_0567_0040, g32p_row17_traceSegment_008_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_008 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 486 81 81, g32p_row17_traceSegment_008_0486_0081, g32p_row17_traceSegment_008_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_008 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 324 162 162, g32p_row17_traceSegment_008_0324_0162, g32p_row17_traceSegment_008_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_008 0 648 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 0 324 324, g32p_row17_traceSegment_008_0000_0324, g32p_row17_traceSegment_008_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 648 10 10, g32p_row17_traceSegment_008_0648_0010, g32p_row17_traceSegment_008_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 668 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 668 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 668 10 10, g32p_row17_traceSegment_008_0668_0010, g32p_row17_traceSegment_008_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 648 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 648 20 20, g32p_row17_traceSegment_008_0648_0020, g32p_row17_traceSegment_008_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 688 10 10, g32p_row17_traceSegment_008_0688_0010, g32p_row17_traceSegment_008_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 708 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 708 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 708 10 11, g32p_row17_traceSegment_008_0708_0010, g32p_row17_traceSegment_008_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 688 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 688 20 21, g32p_row17_traceSegment_008_0688_0020, g32p_row17_traceSegment_008_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 648 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 648 40 41, g32p_row17_traceSegment_008_0648_0040, g32p_row17_traceSegment_008_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 729 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 729 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 729 10 10, g32p_row17_traceSegment_008_0729_0010, g32p_row17_traceSegment_008_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 749 10 10, g32p_row17_traceSegment_008_0749_0010, g32p_row17_traceSegment_008_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 729 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 729 20 20, g32p_row17_traceSegment_008_0729_0020, g32p_row17_traceSegment_008_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 769 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 769 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 769 10 10, g32p_row17_traceSegment_008_0769_0010, g32p_row17_traceSegment_008_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 799 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 789 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 789 10 11, g32p_row17_traceSegment_008_0789_0010, g32p_row17_traceSegment_008_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 769 41 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 769 20 21, g32p_row17_traceSegment_008_0769_0020, g32p_row17_traceSegment_008_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 729 81 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 729 40 41, g32p_row17_traceSegment_008_0729_0040, g32p_row17_traceSegment_008_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_008 648 162 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 648 81 81, g32p_row17_traceSegment_008_0648_0081, g32p_row17_traceSegment_008_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 810 10 10, g32p_row17_traceSegment_008_0810_0010, g32p_row17_traceSegment_008_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 830 10 10, g32p_row17_traceSegment_008_0830_0010, g32p_row17_traceSegment_008_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 810 20 20, g32p_row17_traceSegment_008_0810_0020, g32p_row17_traceSegment_008_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 850 10 10, g32p_row17_traceSegment_008_0850_0010, g32p_row17_traceSegment_008_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 880 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 870 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 870 10 11, g32p_row17_traceSegment_008_0870_0010, g32p_row17_traceSegment_008_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 850 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 850 20 21, g32p_row17_traceSegment_008_0850_0020, g32p_row17_traceSegment_008_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 810 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 810 40 41, g32p_row17_traceSegment_008_0810_0040, g32p_row17_traceSegment_008_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 891 10 10, g32p_row17_traceSegment_008_0891_0010, g32p_row17_traceSegment_008_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 911 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 911 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 911 10 10, g32p_row17_traceSegment_008_0911_0010, g32p_row17_traceSegment_008_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 891 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 891 20 20, g32p_row17_traceSegment_008_0891_0020, g32p_row17_traceSegment_008_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 931 10 10, g32p_row17_traceSegment_008_0931_0010, g32p_row17_traceSegment_008_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 951 10 11, g32p_row17_traceSegment_008_0951_0010, g32p_row17_traceSegment_008_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 931 20 21, g32p_row17_traceSegment_008_0931_0020, g32p_row17_traceSegment_008_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 891 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 891 40 41, g32p_row17_traceSegment_008_0891_0040, g32p_row17_traceSegment_008_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_008 810 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 810 81 81, g32p_row17_traceSegment_008_0810_0081, g32p_row17_traceSegment_008_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_008 648 324 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 648 162 162, g32p_row17_traceSegment_008_0648_0162, g32p_row17_traceSegment_008_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 972 10 10, g32p_row17_traceSegment_008_0972_0010, g32p_row17_traceSegment_008_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 992 10 10, g32p_row17_traceSegment_008_0992_0010, g32p_row17_traceSegment_008_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 972 20 20, g32p_row17_traceSegment_008_0972_0020, g32p_row17_traceSegment_008_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1012 10 10, g32p_row17_traceSegment_008_1012_0010, g32p_row17_traceSegment_008_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1032 10 11, g32p_row17_traceSegment_008_1032_0010, g32p_row17_traceSegment_008_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1012 20 21, g32p_row17_traceSegment_008_1012_0020, g32p_row17_traceSegment_008_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 972 40 41, g32p_row17_traceSegment_008_0972_0040, g32p_row17_traceSegment_008_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1053 10 10, g32p_row17_traceSegment_008_1053_0010, g32p_row17_traceSegment_008_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1073 10 10, g32p_row17_traceSegment_008_1073_0010, g32p_row17_traceSegment_008_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1053 20 20, g32p_row17_traceSegment_008_1053_0020, g32p_row17_traceSegment_008_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1093 10 10, g32p_row17_traceSegment_008_1093_0010, g32p_row17_traceSegment_008_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1113 10 11, g32p_row17_traceSegment_008_1113_0010, g32p_row17_traceSegment_008_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1093 20 21, g32p_row17_traceSegment_008_1093_0020, g32p_row17_traceSegment_008_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1053 40 41, g32p_row17_traceSegment_008_1053_0040, g32p_row17_traceSegment_008_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_008 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 972 81 81, g32p_row17_traceSegment_008_0972_0081, g32p_row17_traceSegment_008_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1134 10 10, g32p_row17_traceSegment_008_1134_0010, g32p_row17_traceSegment_008_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1154 10 10, g32p_row17_traceSegment_008_1154_0010, g32p_row17_traceSegment_008_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1134 20 20, g32p_row17_traceSegment_008_1134_0020, g32p_row17_traceSegment_008_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1174 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 1174 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1174 10 10, g32p_row17_traceSegment_008_1174_0010, g32p_row17_traceSegment_008_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1194 10 11, g32p_row17_traceSegment_008_1194_0010, g32p_row17_traceSegment_008_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 1174 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1174 20 21, g32p_row17_traceSegment_008_1174_0020, g32p_row17_traceSegment_008_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 1134 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1134 40 41, g32p_row17_traceSegment_008_1134_0040, g32p_row17_traceSegment_008_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1215 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 1215 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1215 10 10, g32p_row17_traceSegment_008_1215_0010, g32p_row17_traceSegment_008_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1235 10 10, g32p_row17_traceSegment_008_1235_0010, g32p_row17_traceSegment_008_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_008 1215 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1215 20 20, g32p_row17_traceSegment_008_1215_0020, g32p_row17_traceSegment_008_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_008 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1255 10 10, g32p_row17_traceSegment_008_1255_0010, g32p_row17_traceSegment_008_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_008 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_008 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_008_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_008 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1275 10 11, g32p_row17_traceSegment_008_1275_0010, g32p_row17_traceSegment_008_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_008 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1255 20 21, g32p_row17_traceSegment_008_1255_0020, g32p_row17_traceSegment_008_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_008 1215 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1215 40 41, g32p_row17_traceSegment_008_1215_0040, g32p_row17_traceSegment_008_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_008_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_008 1134 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 1134 81 81, g32p_row17_traceSegment_008_1134_0081, g32p_row17_traceSegment_008_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_008 972 324 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 972 162 162, g32p_row17_traceSegment_008_0972_0162, g32p_row17_traceSegment_008_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_008 648 648 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 648 324 324, g32p_row17_traceSegment_008_0648_0324, g32p_row17_traceSegment_008_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_008_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_008 0 1296 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_008 0 648 648, g32p_row17_traceSegment_008_0000_0648, g32p_row17_traceSegment_008_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_008 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 8 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_008_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_010 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 10 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_010_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 0 10 10, g32p_row17_traceSegment_010_0000_0010, g32p_row17_traceSegment_010_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 20 10 10, g32p_row17_traceSegment_010_0020_0010, g32p_row17_traceSegment_010_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 0 20 20, g32p_row17_traceSegment_010_0000_0020, g32p_row17_traceSegment_010_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 40 10 10, g32p_row17_traceSegment_010_0040_0010, g32p_row17_traceSegment_010_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 60 10 11, g32p_row17_traceSegment_010_0060_0010, g32p_row17_traceSegment_010_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 40 20 21, g32p_row17_traceSegment_010_0040_0020, g32p_row17_traceSegment_010_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 0 40 41, g32p_row17_traceSegment_010_0000_0040, g32p_row17_traceSegment_010_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 81 10 10, g32p_row17_traceSegment_010_0081_0010, g32p_row17_traceSegment_010_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 101 10 10, g32p_row17_traceSegment_010_0101_0010, g32p_row17_traceSegment_010_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 81 20 20, g32p_row17_traceSegment_010_0081_0020, g32p_row17_traceSegment_010_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 121 10 10, g32p_row17_traceSegment_010_0121_0010, g32p_row17_traceSegment_010_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 141 10 11, g32p_row17_traceSegment_010_0141_0010, g32p_row17_traceSegment_010_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 121 20 21, g32p_row17_traceSegment_010_0121_0020, g32p_row17_traceSegment_010_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 81 40 41, g32p_row17_traceSegment_010_0081_0040, g32p_row17_traceSegment_010_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_010 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 0 81 81, g32p_row17_traceSegment_010_0000_0081, g32p_row17_traceSegment_010_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 162 10 10, g32p_row17_traceSegment_010_0162_0010, g32p_row17_traceSegment_010_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 182 10 10, g32p_row17_traceSegment_010_0182_0010, g32p_row17_traceSegment_010_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 162 20 20, g32p_row17_traceSegment_010_0162_0020, g32p_row17_traceSegment_010_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 202 10 10, g32p_row17_traceSegment_010_0202_0010, g32p_row17_traceSegment_010_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 222 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 222 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 222 10 11, g32p_row17_traceSegment_010_0222_0010, g32p_row17_traceSegment_010_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 202 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 202 20 21, g32p_row17_traceSegment_010_0202_0020, g32p_row17_traceSegment_010_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 162 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 162 40 41, g32p_row17_traceSegment_010_0162_0040, g32p_row17_traceSegment_010_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 243 10 10, g32p_row17_traceSegment_010_0243_0010, g32p_row17_traceSegment_010_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 273 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 263 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 263 10 10, g32p_row17_traceSegment_010_0263_0010, g32p_row17_traceSegment_010_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 243 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 243 20 20, g32p_row17_traceSegment_010_0243_0020, g32p_row17_traceSegment_010_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 283 10 10, g32p_row17_traceSegment_010_0283_0010, g32p_row17_traceSegment_010_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 313 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 303 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 303 10 11, g32p_row17_traceSegment_010_0303_0010, g32p_row17_traceSegment_010_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 283 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 283 20 21, g32p_row17_traceSegment_010_0283_0020, g32p_row17_traceSegment_010_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 243 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 243 40 41, g32p_row17_traceSegment_010_0243_0040, g32p_row17_traceSegment_010_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_010 162 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 162 81 81, g32p_row17_traceSegment_010_0162_0081, g32p_row17_traceSegment_010_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_010 0 324 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 0 162 162, g32p_row17_traceSegment_010_0000_0162, g32p_row17_traceSegment_010_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 324 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 324 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 324 10 10, g32p_row17_traceSegment_010_0324_0010, g32p_row17_traceSegment_010_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 354 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 344 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 344 10 10, g32p_row17_traceSegment_010_0344_0010, g32p_row17_traceSegment_010_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 324 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 324 20 20, g32p_row17_traceSegment_010_0324_0020, g32p_row17_traceSegment_010_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 364 10 10, g32p_row17_traceSegment_010_0364_0010, g32p_row17_traceSegment_010_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 384 10 11, g32p_row17_traceSegment_010_0384_0010, g32p_row17_traceSegment_010_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 364 20 21, g32p_row17_traceSegment_010_0364_0020, g32p_row17_traceSegment_010_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 324 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 324 40 41, g32p_row17_traceSegment_010_0324_0040, g32p_row17_traceSegment_010_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 405 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 405 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 405 10 10, g32p_row17_traceSegment_010_0405_0010, g32p_row17_traceSegment_010_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 425 10 10, g32p_row17_traceSegment_010_0425_0010, g32p_row17_traceSegment_010_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 405 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 405 20 20, g32p_row17_traceSegment_010_0405_0020, g32p_row17_traceSegment_010_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 445 10 10, g32p_row17_traceSegment_010_0445_0010, g32p_row17_traceSegment_010_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 465 10 11, g32p_row17_traceSegment_010_0465_0010, g32p_row17_traceSegment_010_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 445 20 21, g32p_row17_traceSegment_010_0445_0020, g32p_row17_traceSegment_010_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 405 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 405 40 41, g32p_row17_traceSegment_010_0405_0040, g32p_row17_traceSegment_010_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_010 324 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 324 81 81, g32p_row17_traceSegment_010_0324_0081, g32p_row17_traceSegment_010_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 486 10 10, g32p_row17_traceSegment_010_0486_0010, g32p_row17_traceSegment_010_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 516 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 506 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 506 10 10, g32p_row17_traceSegment_010_0506_0010, g32p_row17_traceSegment_010_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 486 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 486 20 20, g32p_row17_traceSegment_010_0486_0020, g32p_row17_traceSegment_010_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 526 10 10, g32p_row17_traceSegment_010_0526_0010, g32p_row17_traceSegment_010_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 546 10 11, g32p_row17_traceSegment_010_0546_0010, g32p_row17_traceSegment_010_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 526 20 21, g32p_row17_traceSegment_010_0526_0020, g32p_row17_traceSegment_010_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 486 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 486 40 41, g32p_row17_traceSegment_010_0486_0040, g32p_row17_traceSegment_010_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 567 10 10, g32p_row17_traceSegment_010_0567_0010, g32p_row17_traceSegment_010_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 587 10 10, g32p_row17_traceSegment_010_0587_0010, g32p_row17_traceSegment_010_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 567 20 20, g32p_row17_traceSegment_010_0567_0020, g32p_row17_traceSegment_010_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 607 10 10, g32p_row17_traceSegment_010_0607_0010, g32p_row17_traceSegment_010_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 627 10 11, g32p_row17_traceSegment_010_0627_0010, g32p_row17_traceSegment_010_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 607 20 21, g32p_row17_traceSegment_010_0607_0020, g32p_row17_traceSegment_010_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 567 40 41, g32p_row17_traceSegment_010_0567_0040, g32p_row17_traceSegment_010_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_010 486 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 486 81 81, g32p_row17_traceSegment_010_0486_0081, g32p_row17_traceSegment_010_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_010 324 324 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 324 162 162, g32p_row17_traceSegment_010_0324_0162, g32p_row17_traceSegment_010_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_010 0 648 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 0 324 324, g32p_row17_traceSegment_010_0000_0324, g32p_row17_traceSegment_010_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 648 10 10, g32p_row17_traceSegment_010_0648_0010, g32p_row17_traceSegment_010_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 668 10 10, g32p_row17_traceSegment_010_0668_0010, g32p_row17_traceSegment_010_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 648 20 20, g32p_row17_traceSegment_010_0648_0020, g32p_row17_traceSegment_010_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 688 10 10, g32p_row17_traceSegment_010_0688_0010, g32p_row17_traceSegment_010_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 708 10 11, g32p_row17_traceSegment_010_0708_0010, g32p_row17_traceSegment_010_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 688 20 21, g32p_row17_traceSegment_010_0688_0020, g32p_row17_traceSegment_010_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 648 40 41, g32p_row17_traceSegment_010_0648_0040, g32p_row17_traceSegment_010_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 729 10 10, g32p_row17_traceSegment_010_0729_0010, g32p_row17_traceSegment_010_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 749 10 10, g32p_row17_traceSegment_010_0749_0010, g32p_row17_traceSegment_010_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 729 20 20, g32p_row17_traceSegment_010_0729_0020, g32p_row17_traceSegment_010_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 769 10 10, g32p_row17_traceSegment_010_0769_0010, g32p_row17_traceSegment_010_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 789 10 11, g32p_row17_traceSegment_010_0789_0010, g32p_row17_traceSegment_010_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 769 20 21, g32p_row17_traceSegment_010_0769_0020, g32p_row17_traceSegment_010_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 729 40 41, g32p_row17_traceSegment_010_0729_0040, g32p_row17_traceSegment_010_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_010 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 648 81 81, g32p_row17_traceSegment_010_0648_0081, g32p_row17_traceSegment_010_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 810 10 10, g32p_row17_traceSegment_010_0810_0010, g32p_row17_traceSegment_010_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 830 10 10, g32p_row17_traceSegment_010_0830_0010, g32p_row17_traceSegment_010_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 810 20 20, g32p_row17_traceSegment_010_0810_0020, g32p_row17_traceSegment_010_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 850 10 10, g32p_row17_traceSegment_010_0850_0010, g32p_row17_traceSegment_010_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 870 10 11, g32p_row17_traceSegment_010_0870_0010, g32p_row17_traceSegment_010_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 850 20 21, g32p_row17_traceSegment_010_0850_0020, g32p_row17_traceSegment_010_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 810 40 41, g32p_row17_traceSegment_010_0810_0040, g32p_row17_traceSegment_010_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 891 10 10, g32p_row17_traceSegment_010_0891_0010, g32p_row17_traceSegment_010_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 911 10 10, g32p_row17_traceSegment_010_0911_0010, g32p_row17_traceSegment_010_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 891 20 20, g32p_row17_traceSegment_010_0891_0020, g32p_row17_traceSegment_010_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 931 10 10, g32p_row17_traceSegment_010_0931_0010, g32p_row17_traceSegment_010_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 951 10 11, g32p_row17_traceSegment_010_0951_0010, g32p_row17_traceSegment_010_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 931 20 21, g32p_row17_traceSegment_010_0931_0020, g32p_row17_traceSegment_010_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 891 40 41, g32p_row17_traceSegment_010_0891_0040, g32p_row17_traceSegment_010_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_010 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 810 81 81, g32p_row17_traceSegment_010_0810_0081, g32p_row17_traceSegment_010_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_010 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 648 162 162, g32p_row17_traceSegment_010_0648_0162, g32p_row17_traceSegment_010_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 972 10 10, g32p_row17_traceSegment_010_0972_0010, g32p_row17_traceSegment_010_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 992 10 10, g32p_row17_traceSegment_010_0992_0010, g32p_row17_traceSegment_010_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 972 20 20, g32p_row17_traceSegment_010_0972_0020, g32p_row17_traceSegment_010_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1012 10 10, g32p_row17_traceSegment_010_1012_0010, g32p_row17_traceSegment_010_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1032 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 1042 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 1032 21 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1032 10 11, g32p_row17_traceSegment_010_1032_0010, g32p_row17_traceSegment_010_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 1012 41 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1012 20 21, g32p_row17_traceSegment_010_1012_0020, g32p_row17_traceSegment_010_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 972 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 972 40 41, g32p_row17_traceSegment_010_0972_0040, g32p_row17_traceSegment_010_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1053 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 1053 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1053 10 10, g32p_row17_traceSegment_010_1053_0010, g32p_row17_traceSegment_010_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1073 10 10, g32p_row17_traceSegment_010_1073_0010, g32p_row17_traceSegment_010_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 1053 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1053 20 20, g32p_row17_traceSegment_010_1053_0020, g32p_row17_traceSegment_010_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1093 10 10, g32p_row17_traceSegment_010_1093_0010, g32p_row17_traceSegment_010_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1113 10 11, g32p_row17_traceSegment_010_1113_0010, g32p_row17_traceSegment_010_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1093 20 21, g32p_row17_traceSegment_010_1093_0020, g32p_row17_traceSegment_010_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 1053 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1053 40 41, g32p_row17_traceSegment_010_1053_0040, g32p_row17_traceSegment_010_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_010 972 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 972 81 81, g32p_row17_traceSegment_010_0972_0081, g32p_row17_traceSegment_010_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1134 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 1134 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1134 10 10, g32p_row17_traceSegment_010_1134_0010, g32p_row17_traceSegment_010_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1154 10 10, g32p_row17_traceSegment_010_1154_0010, g32p_row17_traceSegment_010_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 1134 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1134 20 20, g32p_row17_traceSegment_010_1134_0020, g32p_row17_traceSegment_010_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1184 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 1174 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1174 10 10, g32p_row17_traceSegment_010_1174_0010, g32p_row17_traceSegment_010_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1194 10 11, g32p_row17_traceSegment_010_1194_0010, g32p_row17_traceSegment_010_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 1174 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1174 20 21, g32p_row17_traceSegment_010_1174_0020, g32p_row17_traceSegment_010_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 1134 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1134 40 41, g32p_row17_traceSegment_010_1134_0040, g32p_row17_traceSegment_010_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1215 10 10, g32p_row17_traceSegment_010_1215_0010, g32p_row17_traceSegment_010_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1235 10 10, g32p_row17_traceSegment_010_1235_0010, g32p_row17_traceSegment_010_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_010 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1215 20 20, g32p_row17_traceSegment_010_1215_0020, g32p_row17_traceSegment_010_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_010 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1255 10 10, g32p_row17_traceSegment_010_1255_0010, g32p_row17_traceSegment_010_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_010 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_010 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_010_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_010 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1275 10 11, g32p_row17_traceSegment_010_1275_0010, g32p_row17_traceSegment_010_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_010 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1255 20 21, g32p_row17_traceSegment_010_1255_0020, g32p_row17_traceSegment_010_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_010 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1215 40 41, g32p_row17_traceSegment_010_1215_0040, g32p_row17_traceSegment_010_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_010_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_010 1134 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 1134 81 81, g32p_row17_traceSegment_010_1134_0081, g32p_row17_traceSegment_010_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_010 972 324 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 972 162 162, g32p_row17_traceSegment_010_0972_0162, g32p_row17_traceSegment_010_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_010 648 648 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 648 324 324, g32p_row17_traceSegment_010_0648_0324, g32p_row17_traceSegment_010_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_010_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_010 0 1296 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_010 0 648 648, g32p_row17_traceSegment_010_0000_0648, g32p_row17_traceSegment_010_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_010 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 10 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_010_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 0) (g32p_literalTraceValue 16 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_000]
  decide +kernel

theorem g32p_row17_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 1) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 1) (g32p_literalTraceValue 16 1)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_001]
  decide +kernel

theorem g32p_row17_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 2) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 2) (g32p_literalTraceValue 16 2)
      [1, -1, 1] [15552, 15552, 15552] = true := by
  rw [g32p_row17_traceCoefficients_002]
  decide +kernel

theorem g32p_row17_tracePolynomial_003 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 3) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 3) (g32p_literalTraceValue 16 3)
      [1, -1, 1] [5184, 5184, 5184] = true := by
  rw [g32p_row17_traceCoefficients_003]
  decide +kernel

theorem g32p_row17_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 4) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 4) (g32p_literalTraceValue 16 4)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row17_traceCoefficients_004]
  decide +kernel

theorem g32p_row17_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 6) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 6) (g32p_literalTraceValue 16 6)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_006]
  decide +kernel

theorem g32p_row17_tracePolynomial_008 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 8) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 8) (g32p_literalTraceValue 16 8)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_008]
  decide +kernel

theorem g32p_row17_tracePolynomial_010 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 10) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 10) (g32p_literalTraceValue 16 10)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_010]
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

private def g32p_row17_traceSegment_011 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 11 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_011_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 0 10 10, g32p_row17_traceSegment_011_0000_0010, g32p_row17_traceSegment_011_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 20 10 10, g32p_row17_traceSegment_011_0020_0010, g32p_row17_traceSegment_011_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 0 20 20, g32p_row17_traceSegment_011_0000_0020, g32p_row17_traceSegment_011_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 40 10 10, g32p_row17_traceSegment_011_0040_0010, g32p_row17_traceSegment_011_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 60 10 11, g32p_row17_traceSegment_011_0060_0010, g32p_row17_traceSegment_011_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 40 20 21, g32p_row17_traceSegment_011_0040_0020, g32p_row17_traceSegment_011_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 0 40 41, g32p_row17_traceSegment_011_0000_0040, g32p_row17_traceSegment_011_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 81 10 10, g32p_row17_traceSegment_011_0081_0010, g32p_row17_traceSegment_011_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 101 10 10, g32p_row17_traceSegment_011_0101_0010, g32p_row17_traceSegment_011_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 81 20 20, g32p_row17_traceSegment_011_0081_0020, g32p_row17_traceSegment_011_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 121 10 10, g32p_row17_traceSegment_011_0121_0010, g32p_row17_traceSegment_011_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 141 10 11, g32p_row17_traceSegment_011_0141_0010, g32p_row17_traceSegment_011_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 121 20 21, g32p_row17_traceSegment_011_0121_0020, g32p_row17_traceSegment_011_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 81 40 41, g32p_row17_traceSegment_011_0081_0040, g32p_row17_traceSegment_011_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_011 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 0 81 81, g32p_row17_traceSegment_011_0000_0081, g32p_row17_traceSegment_011_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 162 10 10, g32p_row17_traceSegment_011_0162_0010, g32p_row17_traceSegment_011_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 182 10 10, g32p_row17_traceSegment_011_0182_0010, g32p_row17_traceSegment_011_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 162 20 20, g32p_row17_traceSegment_011_0162_0020, g32p_row17_traceSegment_011_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 202 10 10, g32p_row17_traceSegment_011_0202_0010, g32p_row17_traceSegment_011_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 222 10 11, g32p_row17_traceSegment_011_0222_0010, g32p_row17_traceSegment_011_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 202 20 21, g32p_row17_traceSegment_011_0202_0020, g32p_row17_traceSegment_011_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 162 40 41, g32p_row17_traceSegment_011_0162_0040, g32p_row17_traceSegment_011_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 243 10 10, g32p_row17_traceSegment_011_0243_0010, g32p_row17_traceSegment_011_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 263 10 10, g32p_row17_traceSegment_011_0263_0010, g32p_row17_traceSegment_011_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 243 20 20, g32p_row17_traceSegment_011_0243_0020, g32p_row17_traceSegment_011_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 283 10 10, g32p_row17_traceSegment_011_0283_0010, g32p_row17_traceSegment_011_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 303 10 11, g32p_row17_traceSegment_011_0303_0010, g32p_row17_traceSegment_011_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 283 20 21, g32p_row17_traceSegment_011_0283_0020, g32p_row17_traceSegment_011_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 243 40 41, g32p_row17_traceSegment_011_0243_0040, g32p_row17_traceSegment_011_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_011 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 162 81 81, g32p_row17_traceSegment_011_0162_0081, g32p_row17_traceSegment_011_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_011 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 0 162 162, g32p_row17_traceSegment_011_0000_0162, g32p_row17_traceSegment_011_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 324 10 10, g32p_row17_traceSegment_011_0324_0010, g32p_row17_traceSegment_011_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 344 10 10, g32p_row17_traceSegment_011_0344_0010, g32p_row17_traceSegment_011_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 324 20 20, g32p_row17_traceSegment_011_0324_0020, g32p_row17_traceSegment_011_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 364 10 10, g32p_row17_traceSegment_011_0364_0010, g32p_row17_traceSegment_011_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 384 10 11, g32p_row17_traceSegment_011_0384_0010, g32p_row17_traceSegment_011_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 364 20 21, g32p_row17_traceSegment_011_0364_0020, g32p_row17_traceSegment_011_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 324 40 41, g32p_row17_traceSegment_011_0324_0040, g32p_row17_traceSegment_011_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 405 10 10, g32p_row17_traceSegment_011_0405_0010, g32p_row17_traceSegment_011_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 425 10 10, g32p_row17_traceSegment_011_0425_0010, g32p_row17_traceSegment_011_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 405 20 20, g32p_row17_traceSegment_011_0405_0020, g32p_row17_traceSegment_011_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 445 10 10, g32p_row17_traceSegment_011_0445_0010, g32p_row17_traceSegment_011_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 465 10 11, g32p_row17_traceSegment_011_0465_0010, g32p_row17_traceSegment_011_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 445 20 21, g32p_row17_traceSegment_011_0445_0020, g32p_row17_traceSegment_011_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 405 40 41, g32p_row17_traceSegment_011_0405_0040, g32p_row17_traceSegment_011_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_011 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 324 81 81, g32p_row17_traceSegment_011_0324_0081, g32p_row17_traceSegment_011_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 486 10 10, g32p_row17_traceSegment_011_0486_0010, g32p_row17_traceSegment_011_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 506 10 10, g32p_row17_traceSegment_011_0506_0010, g32p_row17_traceSegment_011_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 486 20 20, g32p_row17_traceSegment_011_0486_0020, g32p_row17_traceSegment_011_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 526 10 10, g32p_row17_traceSegment_011_0526_0010, g32p_row17_traceSegment_011_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 546 10 11, g32p_row17_traceSegment_011_0546_0010, g32p_row17_traceSegment_011_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 526 20 21, g32p_row17_traceSegment_011_0526_0020, g32p_row17_traceSegment_011_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 486 40 41, g32p_row17_traceSegment_011_0486_0040, g32p_row17_traceSegment_011_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 567 10 10, g32p_row17_traceSegment_011_0567_0010, g32p_row17_traceSegment_011_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 587 10 10, g32p_row17_traceSegment_011_0587_0010, g32p_row17_traceSegment_011_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 567 20 20, g32p_row17_traceSegment_011_0567_0020, g32p_row17_traceSegment_011_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 607 10 10, g32p_row17_traceSegment_011_0607_0010, g32p_row17_traceSegment_011_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 627 10 11, g32p_row17_traceSegment_011_0627_0010, g32p_row17_traceSegment_011_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 607 20 21, g32p_row17_traceSegment_011_0607_0020, g32p_row17_traceSegment_011_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 567 40 41, g32p_row17_traceSegment_011_0567_0040, g32p_row17_traceSegment_011_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_011 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 486 81 81, g32p_row17_traceSegment_011_0486_0081, g32p_row17_traceSegment_011_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_011 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 324 162 162, g32p_row17_traceSegment_011_0324_0162, g32p_row17_traceSegment_011_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_011 0 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 0 324 324, g32p_row17_traceSegment_011_0000_0324, g32p_row17_traceSegment_011_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 648 10 10, g32p_row17_traceSegment_011_0648_0010, g32p_row17_traceSegment_011_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 668 10 10, g32p_row17_traceSegment_011_0668_0010, g32p_row17_traceSegment_011_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 648 20 20, g32p_row17_traceSegment_011_0648_0020, g32p_row17_traceSegment_011_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 688 10 10, g32p_row17_traceSegment_011_0688_0010, g32p_row17_traceSegment_011_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 708 10 11, g32p_row17_traceSegment_011_0708_0010, g32p_row17_traceSegment_011_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 688 20 21, g32p_row17_traceSegment_011_0688_0020, g32p_row17_traceSegment_011_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 648 40 41, g32p_row17_traceSegment_011_0648_0040, g32p_row17_traceSegment_011_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 729 10 10, g32p_row17_traceSegment_011_0729_0010, g32p_row17_traceSegment_011_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 749 10 10, g32p_row17_traceSegment_011_0749_0010, g32p_row17_traceSegment_011_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 729 20 20, g32p_row17_traceSegment_011_0729_0020, g32p_row17_traceSegment_011_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 769 10 10, g32p_row17_traceSegment_011_0769_0010, g32p_row17_traceSegment_011_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 789 10 11, g32p_row17_traceSegment_011_0789_0010, g32p_row17_traceSegment_011_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 769 20 21, g32p_row17_traceSegment_011_0769_0020, g32p_row17_traceSegment_011_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 729 40 41, g32p_row17_traceSegment_011_0729_0040, g32p_row17_traceSegment_011_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_011 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 648 81 81, g32p_row17_traceSegment_011_0648_0081, g32p_row17_traceSegment_011_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 810 10 10, g32p_row17_traceSegment_011_0810_0010, g32p_row17_traceSegment_011_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 830 10 10, g32p_row17_traceSegment_011_0830_0010, g32p_row17_traceSegment_011_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 810 20 20, g32p_row17_traceSegment_011_0810_0020, g32p_row17_traceSegment_011_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 850 10 10, g32p_row17_traceSegment_011_0850_0010, g32p_row17_traceSegment_011_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 870 10 11, g32p_row17_traceSegment_011_0870_0010, g32p_row17_traceSegment_011_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 850 20 21, g32p_row17_traceSegment_011_0850_0020, g32p_row17_traceSegment_011_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 810 40 41, g32p_row17_traceSegment_011_0810_0040, g32p_row17_traceSegment_011_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 891 10 10, g32p_row17_traceSegment_011_0891_0010, g32p_row17_traceSegment_011_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 911 10 10, g32p_row17_traceSegment_011_0911_0010, g32p_row17_traceSegment_011_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 891 20 20, g32p_row17_traceSegment_011_0891_0020, g32p_row17_traceSegment_011_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 931 10 10, g32p_row17_traceSegment_011_0931_0010, g32p_row17_traceSegment_011_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 951 10 11, g32p_row17_traceSegment_011_0951_0010, g32p_row17_traceSegment_011_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 931 20 21, g32p_row17_traceSegment_011_0931_0020, g32p_row17_traceSegment_011_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 891 40 41, g32p_row17_traceSegment_011_0891_0040, g32p_row17_traceSegment_011_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_011 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 810 81 81, g32p_row17_traceSegment_011_0810_0081, g32p_row17_traceSegment_011_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_011 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 648 162 162, g32p_row17_traceSegment_011_0648_0162, g32p_row17_traceSegment_011_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 972 10 10, g32p_row17_traceSegment_011_0972_0010, g32p_row17_traceSegment_011_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 992 10 10, g32p_row17_traceSegment_011_0992_0010, g32p_row17_traceSegment_011_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 972 20 20, g32p_row17_traceSegment_011_0972_0020, g32p_row17_traceSegment_011_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1012 10 10, g32p_row17_traceSegment_011_1012_0010, g32p_row17_traceSegment_011_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1032 10 11, g32p_row17_traceSegment_011_1032_0010, g32p_row17_traceSegment_011_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1012 20 21, g32p_row17_traceSegment_011_1012_0020, g32p_row17_traceSegment_011_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 972 40 41, g32p_row17_traceSegment_011_0972_0040, g32p_row17_traceSegment_011_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1053 10 10, g32p_row17_traceSegment_011_1053_0010, g32p_row17_traceSegment_011_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1073 10 10, g32p_row17_traceSegment_011_1073_0010, g32p_row17_traceSegment_011_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1053 20 20, g32p_row17_traceSegment_011_1053_0020, g32p_row17_traceSegment_011_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1093 10 10, g32p_row17_traceSegment_011_1093_0010, g32p_row17_traceSegment_011_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1113 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 1123 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 1113 21 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1113 10 11, g32p_row17_traceSegment_011_1113_0010, g32p_row17_traceSegment_011_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 1093 41 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1093 20 21, g32p_row17_traceSegment_011_1093_0020, g32p_row17_traceSegment_011_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 1053 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1053 40 41, g32p_row17_traceSegment_011_1053_0040, g32p_row17_traceSegment_011_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_011 972 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 972 81 81, g32p_row17_traceSegment_011_0972_0081, g32p_row17_traceSegment_011_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1134 10 10, g32p_row17_traceSegment_011_1134_0010, g32p_row17_traceSegment_011_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1154 10 10, g32p_row17_traceSegment_011_1154_0010, g32p_row17_traceSegment_011_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1134 20 20, g32p_row17_traceSegment_011_1134_0020, g32p_row17_traceSegment_011_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1174 10 10, g32p_row17_traceSegment_011_1174_0010, g32p_row17_traceSegment_011_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1194 10 11, g32p_row17_traceSegment_011_1194_0010, g32p_row17_traceSegment_011_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1174 20 21, g32p_row17_traceSegment_011_1174_0020, g32p_row17_traceSegment_011_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1134 40 41, g32p_row17_traceSegment_011_1134_0040, g32p_row17_traceSegment_011_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1215 10 10, g32p_row17_traceSegment_011_1215_0010, g32p_row17_traceSegment_011_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1235 10 10, g32p_row17_traceSegment_011_1235_0010, g32p_row17_traceSegment_011_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_011 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1215 20 20, g32p_row17_traceSegment_011_1215_0020, g32p_row17_traceSegment_011_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1265 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_011 1255 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1255 10 10, g32p_row17_traceSegment_011_1255_0010, g32p_row17_traceSegment_011_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_011 1275 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_011 1285 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_011_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_011 1275 21 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1275 10 11, g32p_row17_traceSegment_011_1275_0010, g32p_row17_traceSegment_011_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_011 1255 41 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1255 20 21, g32p_row17_traceSegment_011_1255_0020, g32p_row17_traceSegment_011_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_011 1215 81 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1215 40 41, g32p_row17_traceSegment_011_1215_0040, g32p_row17_traceSegment_011_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_011_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_011 1134 162 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 1134 81 81, g32p_row17_traceSegment_011_1134_0081, g32p_row17_traceSegment_011_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_011 972 324 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 972 162 162, g32p_row17_traceSegment_011_0972_0162, g32p_row17_traceSegment_011_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_011 648 648 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 648 324 324, g32p_row17_traceSegment_011_0648_0324, g32p_row17_traceSegment_011_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_011_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_011 0 1296 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_011 0 648 648, g32p_row17_traceSegment_011_0000_0648, g32p_row17_traceSegment_011_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 11 = [0, 0, 6] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_011_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_013 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 13 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_013_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 0 10 10, g32p_row17_traceSegment_013_0000_0010, g32p_row17_traceSegment_013_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 20 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 30 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 20 20 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 20 10 10, g32p_row17_traceSegment_013_0020_0010, g32p_row17_traceSegment_013_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 0 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 0 20 20, g32p_row17_traceSegment_013_0000_0020, g32p_row17_traceSegment_013_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 40 10 10, g32p_row17_traceSegment_013_0040_0010, g32p_row17_traceSegment_013_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 60 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 70 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 60 21 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 60 10 11, g32p_row17_traceSegment_013_0060_0010, g32p_row17_traceSegment_013_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 40 41 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 40 20 21, g32p_row17_traceSegment_013_0040_0020, g32p_row17_traceSegment_013_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 0 81 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 0 40 41, g32p_row17_traceSegment_013_0000_0040, g32p_row17_traceSegment_013_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 81 10 10, g32p_row17_traceSegment_013_0081_0010, g32p_row17_traceSegment_013_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 111 10 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 101 20 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 101 10 10, g32p_row17_traceSegment_013_0101_0010, g32p_row17_traceSegment_013_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 81 40 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 81 20 20, g32p_row17_traceSegment_013_0081_0020, g32p_row17_traceSegment_013_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 121 10 10, g32p_row17_traceSegment_013_0121_0010, g32p_row17_traceSegment_013_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 141 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 141 21 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 141 10 11, g32p_row17_traceSegment_013_0141_0010, g32p_row17_traceSegment_013_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 121 41 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 121 20 21, g32p_row17_traceSegment_013_0121_0020, g32p_row17_traceSegment_013_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 81 81 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 81 40 41, g32p_row17_traceSegment_013_0081_0040, g32p_row17_traceSegment_013_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_013 0 162 = [0, 0, 5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 0 81 81, g32p_row17_traceSegment_013_0000_0081, g32p_row17_traceSegment_013_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 162 10 10, g32p_row17_traceSegment_013_0162_0010, g32p_row17_traceSegment_013_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 192 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 182 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 182 10 10, g32p_row17_traceSegment_013_0182_0010, g32p_row17_traceSegment_013_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 162 40 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 162 20 20, g32p_row17_traceSegment_013_0162_0020, g32p_row17_traceSegment_013_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 202 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 202 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 202 10 10, g32p_row17_traceSegment_013_0202_0010, g32p_row17_traceSegment_013_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 222 10 11, g32p_row17_traceSegment_013_0222_0010, g32p_row17_traceSegment_013_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 202 41 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 202 20 21, g32p_row17_traceSegment_013_0202_0020, g32p_row17_traceSegment_013_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 162 81 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 162 40 41, g32p_row17_traceSegment_013_0162_0040, g32p_row17_traceSegment_013_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 243 10 10, g32p_row17_traceSegment_013_0243_0010, g32p_row17_traceSegment_013_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 263 10 10, g32p_row17_traceSegment_013_0263_0010, g32p_row17_traceSegment_013_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 243 20 20, g32p_row17_traceSegment_013_0243_0020, g32p_row17_traceSegment_013_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 283 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 283 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 283 10 10, g32p_row17_traceSegment_013_0283_0010, g32p_row17_traceSegment_013_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 303 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 303 21 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 303 10 11, g32p_row17_traceSegment_013_0303_0010, g32p_row17_traceSegment_013_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 283 41 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 283 20 21, g32p_row17_traceSegment_013_0283_0020, g32p_row17_traceSegment_013_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 243 81 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 243 40 41, g32p_row17_traceSegment_013_0243_0040, g32p_row17_traceSegment_013_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_013 162 162 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 162 81 81, g32p_row17_traceSegment_013_0162_0081, g32p_row17_traceSegment_013_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_013 0 324 = [0, 0, 6, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 0 162 162, g32p_row17_traceSegment_013_0000_0162, g32p_row17_traceSegment_013_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 324 10 10, g32p_row17_traceSegment_013_0324_0010, g32p_row17_traceSegment_013_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 344 10 10, g32p_row17_traceSegment_013_0344_0010, g32p_row17_traceSegment_013_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 324 20 20, g32p_row17_traceSegment_013_0324_0020, g32p_row17_traceSegment_013_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 364 10 10, g32p_row17_traceSegment_013_0364_0010, g32p_row17_traceSegment_013_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 384 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 384 21 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 384 10 11, g32p_row17_traceSegment_013_0384_0010, g32p_row17_traceSegment_013_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 364 41 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 364 20 21, g32p_row17_traceSegment_013_0364_0020, g32p_row17_traceSegment_013_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 324 81 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 324 40 41, g32p_row17_traceSegment_013_0324_0040, g32p_row17_traceSegment_013_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 405 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 405 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 405 10 10, g32p_row17_traceSegment_013_0405_0010, g32p_row17_traceSegment_013_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 435 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 425 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 425 10 10, g32p_row17_traceSegment_013_0425_0010, g32p_row17_traceSegment_013_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 405 40 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 405 20 20, g32p_row17_traceSegment_013_0405_0020, g32p_row17_traceSegment_013_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 445 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 455 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 445 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 445 10 10, g32p_row17_traceSegment_013_0445_0010, g32p_row17_traceSegment_013_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 465 10 11, g32p_row17_traceSegment_013_0465_0010, g32p_row17_traceSegment_013_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 445 41 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 445 20 21, g32p_row17_traceSegment_013_0445_0020, g32p_row17_traceSegment_013_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 405 81 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 405 40 41, g32p_row17_traceSegment_013_0405_0040, g32p_row17_traceSegment_013_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_013 324 162 = [0, 0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 324 81 81, g32p_row17_traceSegment_013_0324_0081, g32p_row17_traceSegment_013_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 496 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 486 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 486 10 10, g32p_row17_traceSegment_013_0486_0010, g32p_row17_traceSegment_013_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 506 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 516 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 506 20 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 506 10 10, g32p_row17_traceSegment_013_0506_0010, g32p_row17_traceSegment_013_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 486 40 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 486 20 20, g32p_row17_traceSegment_013_0486_0020, g32p_row17_traceSegment_013_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 526 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 526 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 526 10 10, g32p_row17_traceSegment_013_0526_0010, g32p_row17_traceSegment_013_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 546 10 11, g32p_row17_traceSegment_013_0546_0010, g32p_row17_traceSegment_013_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 526 41 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 526 20 21, g32p_row17_traceSegment_013_0526_0020, g32p_row17_traceSegment_013_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 486 81 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 486 40 41, g32p_row17_traceSegment_013_0486_0040, g32p_row17_traceSegment_013_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 567 10 10, g32p_row17_traceSegment_013_0567_0010, g32p_row17_traceSegment_013_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 597 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 587 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 587 10 10, g32p_row17_traceSegment_013_0587_0010, g32p_row17_traceSegment_013_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 567 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 567 20 20, g32p_row17_traceSegment_013_0567_0020, g32p_row17_traceSegment_013_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 607 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 607 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 607 10 10, g32p_row17_traceSegment_013_0607_0010, g32p_row17_traceSegment_013_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 637 11 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 627 21 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 627 10 11, g32p_row17_traceSegment_013_0627_0010, g32p_row17_traceSegment_013_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 607 41 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 607 20 21, g32p_row17_traceSegment_013_0607_0020, g32p_row17_traceSegment_013_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 567 81 = [0, 0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 567 40 41, g32p_row17_traceSegment_013_0567_0040, g32p_row17_traceSegment_013_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_013 486 162 = [0, 0, 3, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 486 81 81, g32p_row17_traceSegment_013_0486_0081, g32p_row17_traceSegment_013_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_013 324 324 = [0, 0, 4, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 324 162 162, g32p_row17_traceSegment_013_0324_0162, g32p_row17_traceSegment_013_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_013 0 648 = [0, 0, 10, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 0 324 324, g32p_row17_traceSegment_013_0000_0324, g32p_row17_traceSegment_013_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 658 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 648 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 648 10 10, g32p_row17_traceSegment_013_0648_0010, g32p_row17_traceSegment_013_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 668 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 668 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 668 10 10, g32p_row17_traceSegment_013_0668_0010, g32p_row17_traceSegment_013_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 648 40 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 648 20 20, g32p_row17_traceSegment_013_0648_0020, g32p_row17_traceSegment_013_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 688 10 10, g32p_row17_traceSegment_013_0688_0010, g32p_row17_traceSegment_013_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 708 10 11, g32p_row17_traceSegment_013_0708_0010, g32p_row17_traceSegment_013_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 688 20 21, g32p_row17_traceSegment_013_0688_0020, g32p_row17_traceSegment_013_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 648 81 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 648 40 41, g32p_row17_traceSegment_013_0648_0040, g32p_row17_traceSegment_013_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 729 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 729 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 729 10 10, g32p_row17_traceSegment_013_0729_0010, g32p_row17_traceSegment_013_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 749 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 749 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 749 10 10, g32p_row17_traceSegment_013_0749_0010, g32p_row17_traceSegment_013_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 729 40 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 729 20 20, g32p_row17_traceSegment_013_0729_0020, g32p_row17_traceSegment_013_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 769 10 10, g32p_row17_traceSegment_013_0769_0010, g32p_row17_traceSegment_013_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 799 11 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 789 21 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 789 10 11, g32p_row17_traceSegment_013_0789_0010, g32p_row17_traceSegment_013_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 769 41 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 769 20 21, g32p_row17_traceSegment_013_0769_0020, g32p_row17_traceSegment_013_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 729 81 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 729 40 41, g32p_row17_traceSegment_013_0729_0040, g32p_row17_traceSegment_013_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_013 648 162 = [0, 0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 648 81 81, g32p_row17_traceSegment_013_0648_0081, g32p_row17_traceSegment_013_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 810 10 10, g32p_row17_traceSegment_013_0810_0010, g32p_row17_traceSegment_013_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 830 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 840 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 830 20 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 830 10 10, g32p_row17_traceSegment_013_0830_0010, g32p_row17_traceSegment_013_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 810 40 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 810 20 20, g32p_row17_traceSegment_013_0810_0020, g32p_row17_traceSegment_013_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 850 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 860 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 850 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 850 10 10, g32p_row17_traceSegment_013_0850_0010, g32p_row17_traceSegment_013_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 870 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 880 11 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 870 21 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 870 10 11, g32p_row17_traceSegment_013_0870_0010, g32p_row17_traceSegment_013_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 850 41 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 850 20 21, g32p_row17_traceSegment_013_0850_0020, g32p_row17_traceSegment_013_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 810 81 = [0, 0, 1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 810 40 41, g32p_row17_traceSegment_013_0810_0040, g32p_row17_traceSegment_013_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 901 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 891 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 891 10 10, g32p_row17_traceSegment_013_0891_0010, g32p_row17_traceSegment_013_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 921 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 911 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 911 10 10, g32p_row17_traceSegment_013_0911_0010, g32p_row17_traceSegment_013_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 891 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 891 20 20, g32p_row17_traceSegment_013_0891_0020, g32p_row17_traceSegment_013_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 941 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 931 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 931 10 10, g32p_row17_traceSegment_013_0931_0010, g32p_row17_traceSegment_013_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 951 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 951 21 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 951 10 11, g32p_row17_traceSegment_013_0951_0010, g32p_row17_traceSegment_013_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 931 41 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 931 20 21, g32p_row17_traceSegment_013_0931_0020, g32p_row17_traceSegment_013_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 891 81 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 891 40 41, g32p_row17_traceSegment_013_0891_0040, g32p_row17_traceSegment_013_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_013 810 162 = [0, 0, 3, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 810 81 81, g32p_row17_traceSegment_013_0810_0081, g32p_row17_traceSegment_013_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_013 648 324 = [0, 0, 6, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 648 162 162, g32p_row17_traceSegment_013_0648_0162, g32p_row17_traceSegment_013_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 972 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 982 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 972 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 972 10 10, g32p_row17_traceSegment_013_0972_0010, g32p_row17_traceSegment_013_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 992 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 992 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 992 10 10, g32p_row17_traceSegment_013_0992_0010, g32p_row17_traceSegment_013_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 972 40 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 972 20 20, g32p_row17_traceSegment_013_0972_0020, g32p_row17_traceSegment_013_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1012 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1022 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 1012 20 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1012 10 10, g32p_row17_traceSegment_013_1012_0010, g32p_row17_traceSegment_013_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1032 10 11, g32p_row17_traceSegment_013_1032_0010, g32p_row17_traceSegment_013_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 1012 41 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1012 20 21, g32p_row17_traceSegment_013_1012_0020, g32p_row17_traceSegment_013_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 972 81 = [0, 0, 1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 972 40 41, g32p_row17_traceSegment_013_0972_0040, g32p_row17_traceSegment_013_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1053 10 10, g32p_row17_traceSegment_013_1053_0010, g32p_row17_traceSegment_013_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1073 10 10, g32p_row17_traceSegment_013_1073_0010, g32p_row17_traceSegment_013_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1053 20 20, g32p_row17_traceSegment_013_1053_0020, g32p_row17_traceSegment_013_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1103 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 1093 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1093 10 10, g32p_row17_traceSegment_013_1093_0010, g32p_row17_traceSegment_013_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1113 10 11, g32p_row17_traceSegment_013_1113_0010, g32p_row17_traceSegment_013_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 1093 41 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1093 20 21, g32p_row17_traceSegment_013_1093_0020, g32p_row17_traceSegment_013_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 1053 81 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1053 40 41, g32p_row17_traceSegment_013_1053_0040, g32p_row17_traceSegment_013_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_013 972 162 = [0, 0, 1, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 972 81 81, g32p_row17_traceSegment_013_0972_0081, g32p_row17_traceSegment_013_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1134 10 10, g32p_row17_traceSegment_013_1134_0010, g32p_row17_traceSegment_013_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1154 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 1154 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1154 10 10, g32p_row17_traceSegment_013_1154_0010, g32p_row17_traceSegment_013_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 1134 40 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1134 20 20, g32p_row17_traceSegment_013_1134_0020, g32p_row17_traceSegment_013_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1174 10 10, g32p_row17_traceSegment_013_1174_0010, g32p_row17_traceSegment_013_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 1204 11 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 1194 21 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1194 10 11, g32p_row17_traceSegment_013_1194_0010, g32p_row17_traceSegment_013_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 1174 41 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1174 20 21, g32p_row17_traceSegment_013_1174_0020, g32p_row17_traceSegment_013_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 1134 81 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1134 40 41, g32p_row17_traceSegment_013_1134_0040, g32p_row17_traceSegment_013_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1225 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 1215 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1215 10 10, g32p_row17_traceSegment_013_1215_0010, g32p_row17_traceSegment_013_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1235 10 10, g32p_row17_traceSegment_013_1235_0010, g32p_row17_traceSegment_013_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_013 1215 40 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1215 20 20, g32p_row17_traceSegment_013_1215_0020, g32p_row17_traceSegment_013_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_013 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1255 10 10, g32p_row17_traceSegment_013_1255_0010, g32p_row17_traceSegment_013_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_013 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_013 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_013_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_013 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1275 10 11, g32p_row17_traceSegment_013_1275_0010, g32p_row17_traceSegment_013_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_013 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1255 20 21, g32p_row17_traceSegment_013_1255_0020, g32p_row17_traceSegment_013_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_013 1215 81 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1215 40 41, g32p_row17_traceSegment_013_1215_0040, g32p_row17_traceSegment_013_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_013_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_013 1134 162 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 1134 81 81, g32p_row17_traceSegment_013_1134_0081, g32p_row17_traceSegment_013_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_013 972 324 = [0, 0, 2, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 972 162 162, g32p_row17_traceSegment_013_0972_0162, g32p_row17_traceSegment_013_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_013 648 648 = [0, 0, 8, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 648 324 324, g32p_row17_traceSegment_013_0648_0324, g32p_row17_traceSegment_013_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_013_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_013 0 1296 = [0, 0, 18, 0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_013 0 648 648, g32p_row17_traceSegment_013_0000_0648, g32p_row17_traceSegment_013_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_013 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 13 = [0, 0, 18, 0, 0, 36] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_013_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_015 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 15 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_015_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 0 10 10, g32p_row17_traceSegment_015_0000_0010, g32p_row17_traceSegment_015_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 20 10 10, g32p_row17_traceSegment_015_0020_0010, g32p_row17_traceSegment_015_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 0 20 20, g32p_row17_traceSegment_015_0000_0020, g32p_row17_traceSegment_015_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 40 10 10, g32p_row17_traceSegment_015_0040_0010, g32p_row17_traceSegment_015_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 60 10 11, g32p_row17_traceSegment_015_0060_0010, g32p_row17_traceSegment_015_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 40 20 21, g32p_row17_traceSegment_015_0040_0020, g32p_row17_traceSegment_015_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 0 40 41, g32p_row17_traceSegment_015_0000_0040, g32p_row17_traceSegment_015_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 81 10 10, g32p_row17_traceSegment_015_0081_0010, g32p_row17_traceSegment_015_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 101 10 10, g32p_row17_traceSegment_015_0101_0010, g32p_row17_traceSegment_015_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 81 20 20, g32p_row17_traceSegment_015_0081_0020, g32p_row17_traceSegment_015_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 121 10 10, g32p_row17_traceSegment_015_0121_0010, g32p_row17_traceSegment_015_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 141 10 11, g32p_row17_traceSegment_015_0141_0010, g32p_row17_traceSegment_015_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 121 20 21, g32p_row17_traceSegment_015_0121_0020, g32p_row17_traceSegment_015_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 81 40 41, g32p_row17_traceSegment_015_0081_0040, g32p_row17_traceSegment_015_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_015 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 0 81 81, g32p_row17_traceSegment_015_0000_0081, g32p_row17_traceSegment_015_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 162 10 10, g32p_row17_traceSegment_015_0162_0010, g32p_row17_traceSegment_015_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 182 10 10, g32p_row17_traceSegment_015_0182_0010, g32p_row17_traceSegment_015_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 162 20 20, g32p_row17_traceSegment_015_0162_0020, g32p_row17_traceSegment_015_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 202 10 10, g32p_row17_traceSegment_015_0202_0010, g32p_row17_traceSegment_015_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 222 10 11, g32p_row17_traceSegment_015_0222_0010, g32p_row17_traceSegment_015_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 202 20 21, g32p_row17_traceSegment_015_0202_0020, g32p_row17_traceSegment_015_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 162 40 41, g32p_row17_traceSegment_015_0162_0040, g32p_row17_traceSegment_015_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 243 10 10, g32p_row17_traceSegment_015_0243_0010, g32p_row17_traceSegment_015_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 263 10 10, g32p_row17_traceSegment_015_0263_0010, g32p_row17_traceSegment_015_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 243 20 20, g32p_row17_traceSegment_015_0243_0020, g32p_row17_traceSegment_015_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 283 10 10, g32p_row17_traceSegment_015_0283_0010, g32p_row17_traceSegment_015_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 303 10 11, g32p_row17_traceSegment_015_0303_0010, g32p_row17_traceSegment_015_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 283 20 21, g32p_row17_traceSegment_015_0283_0020, g32p_row17_traceSegment_015_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 243 40 41, g32p_row17_traceSegment_015_0243_0040, g32p_row17_traceSegment_015_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_015 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 162 81 81, g32p_row17_traceSegment_015_0162_0081, g32p_row17_traceSegment_015_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_015 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 0 162 162, g32p_row17_traceSegment_015_0000_0162, g32p_row17_traceSegment_015_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 324 10 10, g32p_row17_traceSegment_015_0324_0010, g32p_row17_traceSegment_015_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 344 10 10, g32p_row17_traceSegment_015_0344_0010, g32p_row17_traceSegment_015_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 324 20 20, g32p_row17_traceSegment_015_0324_0020, g32p_row17_traceSegment_015_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 364 10 10, g32p_row17_traceSegment_015_0364_0010, g32p_row17_traceSegment_015_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 384 10 11, g32p_row17_traceSegment_015_0384_0010, g32p_row17_traceSegment_015_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 364 20 21, g32p_row17_traceSegment_015_0364_0020, g32p_row17_traceSegment_015_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 324 40 41, g32p_row17_traceSegment_015_0324_0040, g32p_row17_traceSegment_015_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 405 10 10, g32p_row17_traceSegment_015_0405_0010, g32p_row17_traceSegment_015_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 425 10 10, g32p_row17_traceSegment_015_0425_0010, g32p_row17_traceSegment_015_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 405 20 20, g32p_row17_traceSegment_015_0405_0020, g32p_row17_traceSegment_015_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 445 10 10, g32p_row17_traceSegment_015_0445_0010, g32p_row17_traceSegment_015_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 465 10 11, g32p_row17_traceSegment_015_0465_0010, g32p_row17_traceSegment_015_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 445 20 21, g32p_row17_traceSegment_015_0445_0020, g32p_row17_traceSegment_015_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 405 40 41, g32p_row17_traceSegment_015_0405_0040, g32p_row17_traceSegment_015_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_015 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 324 81 81, g32p_row17_traceSegment_015_0324_0081, g32p_row17_traceSegment_015_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 486 10 10, g32p_row17_traceSegment_015_0486_0010, g32p_row17_traceSegment_015_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 506 10 10, g32p_row17_traceSegment_015_0506_0010, g32p_row17_traceSegment_015_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 486 20 20, g32p_row17_traceSegment_015_0486_0020, g32p_row17_traceSegment_015_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 526 10 10, g32p_row17_traceSegment_015_0526_0010, g32p_row17_traceSegment_015_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 546 10 11, g32p_row17_traceSegment_015_0546_0010, g32p_row17_traceSegment_015_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 526 20 21, g32p_row17_traceSegment_015_0526_0020, g32p_row17_traceSegment_015_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 486 40 41, g32p_row17_traceSegment_015_0486_0040, g32p_row17_traceSegment_015_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 567 10 10, g32p_row17_traceSegment_015_0567_0010, g32p_row17_traceSegment_015_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 587 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 587 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 587 10 10, g32p_row17_traceSegment_015_0587_0010, g32p_row17_traceSegment_015_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 567 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 567 20 20, g32p_row17_traceSegment_015_0567_0020, g32p_row17_traceSegment_015_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 607 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 607 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 607 10 10, g32p_row17_traceSegment_015_0607_0010, g32p_row17_traceSegment_015_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 627 10 11, g32p_row17_traceSegment_015_0627_0010, g32p_row17_traceSegment_015_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 607 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 607 20 21, g32p_row17_traceSegment_015_0607_0020, g32p_row17_traceSegment_015_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 567 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 567 40 41, g32p_row17_traceSegment_015_0567_0040, g32p_row17_traceSegment_015_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_015 486 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 486 81 81, g32p_row17_traceSegment_015_0486_0081, g32p_row17_traceSegment_015_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_015 324 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 324 162 162, g32p_row17_traceSegment_015_0324_0162, g32p_row17_traceSegment_015_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_015 0 648 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 0 324 324, g32p_row17_traceSegment_015_0000_0324, g32p_row17_traceSegment_015_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 648 10 10, g32p_row17_traceSegment_015_0648_0010, g32p_row17_traceSegment_015_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 668 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 668 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 668 10 10, g32p_row17_traceSegment_015_0668_0010, g32p_row17_traceSegment_015_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 648 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 648 20 20, g32p_row17_traceSegment_015_0648_0020, g32p_row17_traceSegment_015_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 688 10 10, g32p_row17_traceSegment_015_0688_0010, g32p_row17_traceSegment_015_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 718 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 708 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 708 10 11, g32p_row17_traceSegment_015_0708_0010, g32p_row17_traceSegment_015_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 688 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 688 20 21, g32p_row17_traceSegment_015_0688_0020, g32p_row17_traceSegment_015_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 648 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 648 40 41, g32p_row17_traceSegment_015_0648_0040, g32p_row17_traceSegment_015_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 729 10 10, g32p_row17_traceSegment_015_0729_0010, g32p_row17_traceSegment_015_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 759 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 749 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 749 10 10, g32p_row17_traceSegment_015_0749_0010, g32p_row17_traceSegment_015_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 729 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 729 20 20, g32p_row17_traceSegment_015_0729_0020, g32p_row17_traceSegment_015_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 769 10 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 769 20 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 769 10 10, g32p_row17_traceSegment_015_0769_0010, g32p_row17_traceSegment_015_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 789 10 11, g32p_row17_traceSegment_015_0789_0010, g32p_row17_traceSegment_015_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 769 41 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 769 20 21, g32p_row17_traceSegment_015_0769_0020, g32p_row17_traceSegment_015_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 729 81 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 729 40 41, g32p_row17_traceSegment_015_0729_0040, g32p_row17_traceSegment_015_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_015 648 162 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 648 81 81, g32p_row17_traceSegment_015_0648_0081, g32p_row17_traceSegment_015_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 820 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 810 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 810 10 10, g32p_row17_traceSegment_015_0810_0010, g32p_row17_traceSegment_015_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 830 10 10, g32p_row17_traceSegment_015_0830_0010, g32p_row17_traceSegment_015_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 810 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 810 20 20, g32p_row17_traceSegment_015_0810_0020, g32p_row17_traceSegment_015_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 850 10 10, g32p_row17_traceSegment_015_0850_0010, g32p_row17_traceSegment_015_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 870 10 11, g32p_row17_traceSegment_015_0870_0010, g32p_row17_traceSegment_015_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 850 20 21, g32p_row17_traceSegment_015_0850_0020, g32p_row17_traceSegment_015_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 810 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 810 40 41, g32p_row17_traceSegment_015_0810_0040, g32p_row17_traceSegment_015_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 891 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 891 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 891 10 10, g32p_row17_traceSegment_015_0891_0010, g32p_row17_traceSegment_015_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 911 10 10, g32p_row17_traceSegment_015_0911_0010, g32p_row17_traceSegment_015_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 891 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 891 20 20, g32p_row17_traceSegment_015_0891_0020, g32p_row17_traceSegment_015_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 931 10 10, g32p_row17_traceSegment_015_0931_0010, g32p_row17_traceSegment_015_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 951 10 11, g32p_row17_traceSegment_015_0951_0010, g32p_row17_traceSegment_015_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 931 20 21, g32p_row17_traceSegment_015_0931_0020, g32p_row17_traceSegment_015_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 891 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 891 40 41, g32p_row17_traceSegment_015_0891_0040, g32p_row17_traceSegment_015_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_015 810 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 810 81 81, g32p_row17_traceSegment_015_0810_0081, g32p_row17_traceSegment_015_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_015 648 324 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 648 162 162, g32p_row17_traceSegment_015_0648_0162, g32p_row17_traceSegment_015_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 972 10 10, g32p_row17_traceSegment_015_0972_0010, g32p_row17_traceSegment_015_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 992 10 10, g32p_row17_traceSegment_015_0992_0010, g32p_row17_traceSegment_015_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 972 20 20, g32p_row17_traceSegment_015_0972_0020, g32p_row17_traceSegment_015_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1012 10 10, g32p_row17_traceSegment_015_1012_0010, g32p_row17_traceSegment_015_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1032 10 11, g32p_row17_traceSegment_015_1032_0010, g32p_row17_traceSegment_015_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1012 20 21, g32p_row17_traceSegment_015_1012_0020, g32p_row17_traceSegment_015_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 972 40 41, g32p_row17_traceSegment_015_0972_0040, g32p_row17_traceSegment_015_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1053 10 10, g32p_row17_traceSegment_015_1053_0010, g32p_row17_traceSegment_015_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1073 10 10, g32p_row17_traceSegment_015_1073_0010, g32p_row17_traceSegment_015_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1053 20 20, g32p_row17_traceSegment_015_1053_0020, g32p_row17_traceSegment_015_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1093 10 10, g32p_row17_traceSegment_015_1093_0010, g32p_row17_traceSegment_015_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1113 10 11, g32p_row17_traceSegment_015_1113_0010, g32p_row17_traceSegment_015_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1093 20 21, g32p_row17_traceSegment_015_1093_0020, g32p_row17_traceSegment_015_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1053 40 41, g32p_row17_traceSegment_015_1053_0040, g32p_row17_traceSegment_015_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_015 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 972 81 81, g32p_row17_traceSegment_015_0972_0081, g32p_row17_traceSegment_015_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1134 10 10, g32p_row17_traceSegment_015_1134_0010, g32p_row17_traceSegment_015_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1154 10 10, g32p_row17_traceSegment_015_1154_0010, g32p_row17_traceSegment_015_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1134 20 20, g32p_row17_traceSegment_015_1134_0020, g32p_row17_traceSegment_015_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1174 10 10, g32p_row17_traceSegment_015_1174_0010, g32p_row17_traceSegment_015_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1194 10 11, g32p_row17_traceSegment_015_1194_0010, g32p_row17_traceSegment_015_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1174 20 21, g32p_row17_traceSegment_015_1174_0020, g32p_row17_traceSegment_015_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1134 40 41, g32p_row17_traceSegment_015_1134_0040, g32p_row17_traceSegment_015_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1215 10 10, g32p_row17_traceSegment_015_1215_0010, g32p_row17_traceSegment_015_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1235 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 1235 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1235 10 10, g32p_row17_traceSegment_015_1235_0010, g32p_row17_traceSegment_015_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_015 1215 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1215 20 20, g32p_row17_traceSegment_015_1215_0020, g32p_row17_traceSegment_015_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_015 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1255 10 10, g32p_row17_traceSegment_015_1255_0010, g32p_row17_traceSegment_015_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_015 1275 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_015 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_015_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_015 1275 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1275 10 11, g32p_row17_traceSegment_015_1275_0010, g32p_row17_traceSegment_015_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_015 1255 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1255 20 21, g32p_row17_traceSegment_015_1255_0020, g32p_row17_traceSegment_015_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_015 1215 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1215 40 41, g32p_row17_traceSegment_015_1215_0040, g32p_row17_traceSegment_015_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_015_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_015 1134 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 1134 81 81, g32p_row17_traceSegment_015_1134_0081, g32p_row17_traceSegment_015_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_015 972 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 972 162 162, g32p_row17_traceSegment_015_0972_0162, g32p_row17_traceSegment_015_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_015 648 648 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 648 324 324, g32p_row17_traceSegment_015_0648_0324, g32p_row17_traceSegment_015_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_015_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_015 0 1296 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_015 0 648 648, g32p_row17_traceSegment_015_0000_0648, g32p_row17_traceSegment_015_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_015 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 15 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_015_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_018 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 18 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_018_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 10 10 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 0 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 0 10 10, g32p_row17_traceSegment_018_0000_0010, g32p_row17_traceSegment_018_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 30 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 20 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 20 10 10, g32p_row17_traceSegment_018_0020_0010, g32p_row17_traceSegment_018_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 0 40 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 0 20 20, g32p_row17_traceSegment_018_0000_0020, g32p_row17_traceSegment_018_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 40 10 10, g32p_row17_traceSegment_018_0040_0010, g32p_row17_traceSegment_018_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 60 10 11, g32p_row17_traceSegment_018_0060_0010, g32p_row17_traceSegment_018_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 40 20 21, g32p_row17_traceSegment_018_0040_0020, g32p_row17_traceSegment_018_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 0 81 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 0 40 41, g32p_row17_traceSegment_018_0000_0040, g32p_row17_traceSegment_018_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 81 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 81 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 81 10 10, g32p_row17_traceSegment_018_0081_0010, g32p_row17_traceSegment_018_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 101 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 101 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 101 10 10, g32p_row17_traceSegment_018_0101_0010, g32p_row17_traceSegment_018_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 81 40 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 81 20 20, g32p_row17_traceSegment_018_0081_0020, g32p_row17_traceSegment_018_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 121 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 121 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 121 10 10, g32p_row17_traceSegment_018_0121_0010, g32p_row17_traceSegment_018_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 141 10 11, g32p_row17_traceSegment_018_0141_0010, g32p_row17_traceSegment_018_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 121 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 121 20 21, g32p_row17_traceSegment_018_0121_0020, g32p_row17_traceSegment_018_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 81 81 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 81 40 41, g32p_row17_traceSegment_018_0081_0040, g32p_row17_traceSegment_018_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_018 0 162 = [6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 0 81 81, g32p_row17_traceSegment_018_0000_0081, g32p_row17_traceSegment_018_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 162 10 10, g32p_row17_traceSegment_018_0162_0010, g32p_row17_traceSegment_018_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 182 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 182 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 182 10 10, g32p_row17_traceSegment_018_0182_0010, g32p_row17_traceSegment_018_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 162 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 162 20 20, g32p_row17_traceSegment_018_0162_0020, g32p_row17_traceSegment_018_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 212 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 202 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 202 10 10, g32p_row17_traceSegment_018_0202_0010, g32p_row17_traceSegment_018_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 222 10 11, g32p_row17_traceSegment_018_0222_0010, g32p_row17_traceSegment_018_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 202 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 202 20 21, g32p_row17_traceSegment_018_0202_0020, g32p_row17_traceSegment_018_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 162 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 162 40 41, g32p_row17_traceSegment_018_0162_0040, g32p_row17_traceSegment_018_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 243 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 243 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 243 10 10, g32p_row17_traceSegment_018_0243_0010, g32p_row17_traceSegment_018_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 263 10 10, g32p_row17_traceSegment_018_0263_0010, g32p_row17_traceSegment_018_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 243 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 243 20 20, g32p_row17_traceSegment_018_0243_0020, g32p_row17_traceSegment_018_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 283 10 10, g32p_row17_traceSegment_018_0283_0010, g32p_row17_traceSegment_018_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 303 10 11, g32p_row17_traceSegment_018_0303_0010, g32p_row17_traceSegment_018_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 283 20 21, g32p_row17_traceSegment_018_0283_0020, g32p_row17_traceSegment_018_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 243 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 243 40 41, g32p_row17_traceSegment_018_0243_0040, g32p_row17_traceSegment_018_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_018 162 162 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 162 81 81, g32p_row17_traceSegment_018_0162_0081, g32p_row17_traceSegment_018_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_018 0 324 = [9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 0 162 162, g32p_row17_traceSegment_018_0000_0162, g32p_row17_traceSegment_018_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 334 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 324 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 324 10 10, g32p_row17_traceSegment_018_0324_0010, g32p_row17_traceSegment_018_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 344 10 10, g32p_row17_traceSegment_018_0344_0010, g32p_row17_traceSegment_018_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 324 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 324 20 20, g32p_row17_traceSegment_018_0324_0020, g32p_row17_traceSegment_018_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 364 10 10, g32p_row17_traceSegment_018_0364_0010, g32p_row17_traceSegment_018_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 384 10 11, g32p_row17_traceSegment_018_0384_0010, g32p_row17_traceSegment_018_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 364 20 21, g32p_row17_traceSegment_018_0364_0020, g32p_row17_traceSegment_018_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 324 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 324 40 41, g32p_row17_traceSegment_018_0324_0040, g32p_row17_traceSegment_018_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 405 10 10, g32p_row17_traceSegment_018_0405_0010, g32p_row17_traceSegment_018_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 425 10 10, g32p_row17_traceSegment_018_0425_0010, g32p_row17_traceSegment_018_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 405 20 20, g32p_row17_traceSegment_018_0405_0020, g32p_row17_traceSegment_018_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 445 10 10, g32p_row17_traceSegment_018_0445_0010, g32p_row17_traceSegment_018_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 465 10 11, g32p_row17_traceSegment_018_0465_0010, g32p_row17_traceSegment_018_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 445 20 21, g32p_row17_traceSegment_018_0445_0020, g32p_row17_traceSegment_018_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 405 40 41, g32p_row17_traceSegment_018_0405_0040, g32p_row17_traceSegment_018_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_018 324 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 324 81 81, g32p_row17_traceSegment_018_0324_0081, g32p_row17_traceSegment_018_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 486 10 10, g32p_row17_traceSegment_018_0486_0010, g32p_row17_traceSegment_018_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 506 10 10, g32p_row17_traceSegment_018_0506_0010, g32p_row17_traceSegment_018_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 486 20 20, g32p_row17_traceSegment_018_0486_0020, g32p_row17_traceSegment_018_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 526 10 10, g32p_row17_traceSegment_018_0526_0010, g32p_row17_traceSegment_018_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 556 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 546 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 546 10 11, g32p_row17_traceSegment_018_0546_0010, g32p_row17_traceSegment_018_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 526 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 526 20 21, g32p_row17_traceSegment_018_0526_0020, g32p_row17_traceSegment_018_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 486 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 486 40 41, g32p_row17_traceSegment_018_0486_0040, g32p_row17_traceSegment_018_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 567 10 10, g32p_row17_traceSegment_018_0567_0010, g32p_row17_traceSegment_018_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 587 10 10, g32p_row17_traceSegment_018_0587_0010, g32p_row17_traceSegment_018_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 567 20 20, g32p_row17_traceSegment_018_0567_0020, g32p_row17_traceSegment_018_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 607 10 10, g32p_row17_traceSegment_018_0607_0010, g32p_row17_traceSegment_018_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 627 10 11, g32p_row17_traceSegment_018_0627_0010, g32p_row17_traceSegment_018_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 607 20 21, g32p_row17_traceSegment_018_0607_0020, g32p_row17_traceSegment_018_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 567 40 41, g32p_row17_traceSegment_018_0567_0040, g32p_row17_traceSegment_018_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_018 486 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 486 81 81, g32p_row17_traceSegment_018_0486_0081, g32p_row17_traceSegment_018_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_018 324 324 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 324 162 162, g32p_row17_traceSegment_018_0324_0162, g32p_row17_traceSegment_018_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_018 0 648 = [11] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 0 324 324, g32p_row17_traceSegment_018_0000_0324, g32p_row17_traceSegment_018_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 658 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 648 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 648 10 10, g32p_row17_traceSegment_018_0648_0010, g32p_row17_traceSegment_018_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 668 10 10, g32p_row17_traceSegment_018_0668_0010, g32p_row17_traceSegment_018_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 648 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 648 20 20, g32p_row17_traceSegment_018_0648_0020, g32p_row17_traceSegment_018_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 688 10 10, g32p_row17_traceSegment_018_0688_0010, g32p_row17_traceSegment_018_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 708 10 11, g32p_row17_traceSegment_018_0708_0010, g32p_row17_traceSegment_018_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 688 20 21, g32p_row17_traceSegment_018_0688_0020, g32p_row17_traceSegment_018_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 648 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 648 40 41, g32p_row17_traceSegment_018_0648_0040, g32p_row17_traceSegment_018_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 729 10 10, g32p_row17_traceSegment_018_0729_0010, g32p_row17_traceSegment_018_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 749 10 10, g32p_row17_traceSegment_018_0749_0010, g32p_row17_traceSegment_018_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 729 20 20, g32p_row17_traceSegment_018_0729_0020, g32p_row17_traceSegment_018_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 769 10 10, g32p_row17_traceSegment_018_0769_0010, g32p_row17_traceSegment_018_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 789 10 11, g32p_row17_traceSegment_018_0789_0010, g32p_row17_traceSegment_018_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 769 20 21, g32p_row17_traceSegment_018_0769_0020, g32p_row17_traceSegment_018_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 729 40 41, g32p_row17_traceSegment_018_0729_0040, g32p_row17_traceSegment_018_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_018 648 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 648 81 81, g32p_row17_traceSegment_018_0648_0081, g32p_row17_traceSegment_018_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 810 10 10, g32p_row17_traceSegment_018_0810_0010, g32p_row17_traceSegment_018_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 830 10 10, g32p_row17_traceSegment_018_0830_0010, g32p_row17_traceSegment_018_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 810 20 20, g32p_row17_traceSegment_018_0810_0020, g32p_row17_traceSegment_018_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 850 10 10, g32p_row17_traceSegment_018_0850_0010, g32p_row17_traceSegment_018_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 870 10 11, g32p_row17_traceSegment_018_0870_0010, g32p_row17_traceSegment_018_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 850 20 21, g32p_row17_traceSegment_018_0850_0020, g32p_row17_traceSegment_018_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 810 40 41, g32p_row17_traceSegment_018_0810_0040, g32p_row17_traceSegment_018_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 891 10 10, g32p_row17_traceSegment_018_0891_0010, g32p_row17_traceSegment_018_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 911 10 10, g32p_row17_traceSegment_018_0911_0010, g32p_row17_traceSegment_018_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 891 20 20, g32p_row17_traceSegment_018_0891_0020, g32p_row17_traceSegment_018_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 931 10 10, g32p_row17_traceSegment_018_0931_0010, g32p_row17_traceSegment_018_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 951 10 11, g32p_row17_traceSegment_018_0951_0010, g32p_row17_traceSegment_018_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 931 20 21, g32p_row17_traceSegment_018_0931_0020, g32p_row17_traceSegment_018_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 891 40 41, g32p_row17_traceSegment_018_0891_0040, g32p_row17_traceSegment_018_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_018 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 810 81 81, g32p_row17_traceSegment_018_0810_0081, g32p_row17_traceSegment_018_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_018 648 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 648 162 162, g32p_row17_traceSegment_018_0648_0162, g32p_row17_traceSegment_018_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 972 10 10, g32p_row17_traceSegment_018_0972_0010, g32p_row17_traceSegment_018_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 992 10 10, g32p_row17_traceSegment_018_0992_0010, g32p_row17_traceSegment_018_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 972 20 20, g32p_row17_traceSegment_018_0972_0020, g32p_row17_traceSegment_018_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1012 10 10, g32p_row17_traceSegment_018_1012_0010, g32p_row17_traceSegment_018_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1032 10 11, g32p_row17_traceSegment_018_1032_0010, g32p_row17_traceSegment_018_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1012 20 21, g32p_row17_traceSegment_018_1012_0020, g32p_row17_traceSegment_018_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 972 40 41, g32p_row17_traceSegment_018_0972_0040, g32p_row17_traceSegment_018_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1053 10 10, g32p_row17_traceSegment_018_1053_0010, g32p_row17_traceSegment_018_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1073 10 10, g32p_row17_traceSegment_018_1073_0010, g32p_row17_traceSegment_018_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1053 20 20, g32p_row17_traceSegment_018_1053_0020, g32p_row17_traceSegment_018_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1093 10 10, g32p_row17_traceSegment_018_1093_0010, g32p_row17_traceSegment_018_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1113 10 11, g32p_row17_traceSegment_018_1113_0010, g32p_row17_traceSegment_018_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1093 20 21, g32p_row17_traceSegment_018_1093_0020, g32p_row17_traceSegment_018_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1053 40 41, g32p_row17_traceSegment_018_1053_0040, g32p_row17_traceSegment_018_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_018 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 972 81 81, g32p_row17_traceSegment_018_0972_0081, g32p_row17_traceSegment_018_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1134 10 10, g32p_row17_traceSegment_018_1134_0010, g32p_row17_traceSegment_018_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1154 10 10, g32p_row17_traceSegment_018_1154_0010, g32p_row17_traceSegment_018_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1134 20 20, g32p_row17_traceSegment_018_1134_0020, g32p_row17_traceSegment_018_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1174 10 10, g32p_row17_traceSegment_018_1174_0010, g32p_row17_traceSegment_018_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1194 10 11, g32p_row17_traceSegment_018_1194_0010, g32p_row17_traceSegment_018_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1174 20 21, g32p_row17_traceSegment_018_1174_0020, g32p_row17_traceSegment_018_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1134 40 41, g32p_row17_traceSegment_018_1134_0040, g32p_row17_traceSegment_018_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1215 10 10, g32p_row17_traceSegment_018_1215_0010, g32p_row17_traceSegment_018_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1235 10 10, g32p_row17_traceSegment_018_1235_0010, g32p_row17_traceSegment_018_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_018 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1215 20 20, g32p_row17_traceSegment_018_1215_0020, g32p_row17_traceSegment_018_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_018 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1255 10 10, g32p_row17_traceSegment_018_1255_0010, g32p_row17_traceSegment_018_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_018 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_018 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_018_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_018 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1275 10 11, g32p_row17_traceSegment_018_1275_0010, g32p_row17_traceSegment_018_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_018 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1255 20 21, g32p_row17_traceSegment_018_1255_0020, g32p_row17_traceSegment_018_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_018 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1215 40 41, g32p_row17_traceSegment_018_1215_0040, g32p_row17_traceSegment_018_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_018_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_018 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 1134 81 81, g32p_row17_traceSegment_018_1134_0081, g32p_row17_traceSegment_018_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_018 972 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 972 162 162, g32p_row17_traceSegment_018_0972_0162, g32p_row17_traceSegment_018_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_018 648 648 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 648 324 324, g32p_row17_traceSegment_018_0648_0324, g32p_row17_traceSegment_018_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_018_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_018 0 1296 = [12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_018 0 648 648, g32p_row17_traceSegment_018_0000_0648, g32p_row17_traceSegment_018_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 18 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_018_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_019 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 19 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_019_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 0 10 10, g32p_row17_traceSegment_019_0000_0010, g32p_row17_traceSegment_019_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 20 10 10, g32p_row17_traceSegment_019_0020_0010, g32p_row17_traceSegment_019_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 0 20 20, g32p_row17_traceSegment_019_0000_0020, g32p_row17_traceSegment_019_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 40 10 10, g32p_row17_traceSegment_019_0040_0010, g32p_row17_traceSegment_019_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 60 10 11, g32p_row17_traceSegment_019_0060_0010, g32p_row17_traceSegment_019_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 40 20 21, g32p_row17_traceSegment_019_0040_0020, g32p_row17_traceSegment_019_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 0 40 41, g32p_row17_traceSegment_019_0000_0040, g32p_row17_traceSegment_019_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 81 10 10, g32p_row17_traceSegment_019_0081_0010, g32p_row17_traceSegment_019_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 101 10 10, g32p_row17_traceSegment_019_0101_0010, g32p_row17_traceSegment_019_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 81 20 20, g32p_row17_traceSegment_019_0081_0020, g32p_row17_traceSegment_019_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 121 10 10, g32p_row17_traceSegment_019_0121_0010, g32p_row17_traceSegment_019_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 141 10 11, g32p_row17_traceSegment_019_0141_0010, g32p_row17_traceSegment_019_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 121 20 21, g32p_row17_traceSegment_019_0121_0020, g32p_row17_traceSegment_019_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 81 40 41, g32p_row17_traceSegment_019_0081_0040, g32p_row17_traceSegment_019_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_019 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 0 81 81, g32p_row17_traceSegment_019_0000_0081, g32p_row17_traceSegment_019_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 162 10 10, g32p_row17_traceSegment_019_0162_0010, g32p_row17_traceSegment_019_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 182 10 10, g32p_row17_traceSegment_019_0182_0010, g32p_row17_traceSegment_019_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 162 20 20, g32p_row17_traceSegment_019_0162_0020, g32p_row17_traceSegment_019_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 202 10 10, g32p_row17_traceSegment_019_0202_0010, g32p_row17_traceSegment_019_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 222 10 11, g32p_row17_traceSegment_019_0222_0010, g32p_row17_traceSegment_019_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 202 20 21, g32p_row17_traceSegment_019_0202_0020, g32p_row17_traceSegment_019_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 162 40 41, g32p_row17_traceSegment_019_0162_0040, g32p_row17_traceSegment_019_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 253 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 243 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 243 10 10, g32p_row17_traceSegment_019_0243_0010, g32p_row17_traceSegment_019_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 263 10 10, g32p_row17_traceSegment_019_0263_0010, g32p_row17_traceSegment_019_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 243 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 243 20 20, g32p_row17_traceSegment_019_0243_0020, g32p_row17_traceSegment_019_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 283 10 10, g32p_row17_traceSegment_019_0283_0010, g32p_row17_traceSegment_019_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 303 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 303 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 303 10 11, g32p_row17_traceSegment_019_0303_0010, g32p_row17_traceSegment_019_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 283 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 283 20 21, g32p_row17_traceSegment_019_0283_0020, g32p_row17_traceSegment_019_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 243 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 243 40 41, g32p_row17_traceSegment_019_0243_0040, g32p_row17_traceSegment_019_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_019 162 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 162 81 81, g32p_row17_traceSegment_019_0162_0081, g32p_row17_traceSegment_019_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_019 0 324 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 0 162 162, g32p_row17_traceSegment_019_0000_0162, g32p_row17_traceSegment_019_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 324 10 10, g32p_row17_traceSegment_019_0324_0010, g32p_row17_traceSegment_019_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 354 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 344 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 344 10 10, g32p_row17_traceSegment_019_0344_0010, g32p_row17_traceSegment_019_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 324 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 324 20 20, g32p_row17_traceSegment_019_0324_0020, g32p_row17_traceSegment_019_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 364 10 10, g32p_row17_traceSegment_019_0364_0010, g32p_row17_traceSegment_019_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 384 10 11, g32p_row17_traceSegment_019_0384_0010, g32p_row17_traceSegment_019_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 364 20 21, g32p_row17_traceSegment_019_0364_0020, g32p_row17_traceSegment_019_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 324 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 324 40 41, g32p_row17_traceSegment_019_0324_0040, g32p_row17_traceSegment_019_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 405 10 10, g32p_row17_traceSegment_019_0405_0010, g32p_row17_traceSegment_019_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 425 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 425 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 425 10 10, g32p_row17_traceSegment_019_0425_0010, g32p_row17_traceSegment_019_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 405 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 405 20 20, g32p_row17_traceSegment_019_0405_0020, g32p_row17_traceSegment_019_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 445 10 10, g32p_row17_traceSegment_019_0445_0010, g32p_row17_traceSegment_019_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 465 10 11, g32p_row17_traceSegment_019_0465_0010, g32p_row17_traceSegment_019_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 445 20 21, g32p_row17_traceSegment_019_0445_0020, g32p_row17_traceSegment_019_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 405 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 405 40 41, g32p_row17_traceSegment_019_0405_0040, g32p_row17_traceSegment_019_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_019 324 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 324 81 81, g32p_row17_traceSegment_019_0324_0081, g32p_row17_traceSegment_019_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 486 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 486 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 486 10 10, g32p_row17_traceSegment_019_0486_0010, g32p_row17_traceSegment_019_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 506 10 10, g32p_row17_traceSegment_019_0506_0010, g32p_row17_traceSegment_019_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 486 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 486 20 20, g32p_row17_traceSegment_019_0486_0020, g32p_row17_traceSegment_019_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 526 10 10, g32p_row17_traceSegment_019_0526_0010, g32p_row17_traceSegment_019_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 546 10 11, g32p_row17_traceSegment_019_0546_0010, g32p_row17_traceSegment_019_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 526 20 21, g32p_row17_traceSegment_019_0526_0020, g32p_row17_traceSegment_019_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 486 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 486 40 41, g32p_row17_traceSegment_019_0486_0040, g32p_row17_traceSegment_019_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 567 10 10, g32p_row17_traceSegment_019_0567_0010, g32p_row17_traceSegment_019_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 587 10 10, g32p_row17_traceSegment_019_0587_0010, g32p_row17_traceSegment_019_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 567 20 20, g32p_row17_traceSegment_019_0567_0020, g32p_row17_traceSegment_019_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 607 10 10, g32p_row17_traceSegment_019_0607_0010, g32p_row17_traceSegment_019_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 637 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 627 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 627 10 11, g32p_row17_traceSegment_019_0627_0010, g32p_row17_traceSegment_019_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 607 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 607 20 21, g32p_row17_traceSegment_019_0607_0020, g32p_row17_traceSegment_019_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 567 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 567 40 41, g32p_row17_traceSegment_019_0567_0040, g32p_row17_traceSegment_019_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_019 486 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 486 81 81, g32p_row17_traceSegment_019_0486_0081, g32p_row17_traceSegment_019_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_019 324 324 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 324 162 162, g32p_row17_traceSegment_019_0324_0162, g32p_row17_traceSegment_019_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_019 0 648 = [6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 0 324 324, g32p_row17_traceSegment_019_0000_0324, g32p_row17_traceSegment_019_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 658 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 648 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 648 10 10, g32p_row17_traceSegment_019_0648_0010, g32p_row17_traceSegment_019_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 668 10 10, g32p_row17_traceSegment_019_0668_0010, g32p_row17_traceSegment_019_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 648 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 648 20 20, g32p_row17_traceSegment_019_0648_0020, g32p_row17_traceSegment_019_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 688 10 10, g32p_row17_traceSegment_019_0688_0010, g32p_row17_traceSegment_019_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 718 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 708 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 708 10 11, g32p_row17_traceSegment_019_0708_0010, g32p_row17_traceSegment_019_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 688 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 688 20 21, g32p_row17_traceSegment_019_0688_0020, g32p_row17_traceSegment_019_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 648 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 648 40 41, g32p_row17_traceSegment_019_0648_0040, g32p_row17_traceSegment_019_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 739 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 729 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 729 10 10, g32p_row17_traceSegment_019_0729_0010, g32p_row17_traceSegment_019_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 749 10 10, g32p_row17_traceSegment_019_0749_0010, g32p_row17_traceSegment_019_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 729 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 729 20 20, g32p_row17_traceSegment_019_0729_0020, g32p_row17_traceSegment_019_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 769 10 10, g32p_row17_traceSegment_019_0769_0010, g32p_row17_traceSegment_019_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 789 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 789 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 789 10 11, g32p_row17_traceSegment_019_0789_0010, g32p_row17_traceSegment_019_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 769 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 769 20 21, g32p_row17_traceSegment_019_0769_0020, g32p_row17_traceSegment_019_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 729 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 729 40 41, g32p_row17_traceSegment_019_0729_0040, g32p_row17_traceSegment_019_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_019 648 162 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 648 81 81, g32p_row17_traceSegment_019_0648_0081, g32p_row17_traceSegment_019_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 810 10 10, g32p_row17_traceSegment_019_0810_0010, g32p_row17_traceSegment_019_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 840 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 830 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 830 10 10, g32p_row17_traceSegment_019_0830_0010, g32p_row17_traceSegment_019_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 810 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 810 20 20, g32p_row17_traceSegment_019_0810_0020, g32p_row17_traceSegment_019_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 850 10 10, g32p_row17_traceSegment_019_0850_0010, g32p_row17_traceSegment_019_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 870 10 11, g32p_row17_traceSegment_019_0870_0010, g32p_row17_traceSegment_019_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 850 20 21, g32p_row17_traceSegment_019_0850_0020, g32p_row17_traceSegment_019_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 810 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 810 40 41, g32p_row17_traceSegment_019_0810_0040, g32p_row17_traceSegment_019_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 891 10 10, g32p_row17_traceSegment_019_0891_0010, g32p_row17_traceSegment_019_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 911 10 10, g32p_row17_traceSegment_019_0911_0010, g32p_row17_traceSegment_019_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 891 20 20, g32p_row17_traceSegment_019_0891_0020, g32p_row17_traceSegment_019_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 931 10 10, g32p_row17_traceSegment_019_0931_0010, g32p_row17_traceSegment_019_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 951 10 11, g32p_row17_traceSegment_019_0951_0010, g32p_row17_traceSegment_019_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 931 20 21, g32p_row17_traceSegment_019_0931_0020, g32p_row17_traceSegment_019_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 891 40 41, g32p_row17_traceSegment_019_0891_0040, g32p_row17_traceSegment_019_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_019 810 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 810 81 81, g32p_row17_traceSegment_019_0810_0081, g32p_row17_traceSegment_019_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_019 648 324 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 648 162 162, g32p_row17_traceSegment_019_0648_0162, g32p_row17_traceSegment_019_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 982 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 972 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 972 10 10, g32p_row17_traceSegment_019_0972_0010, g32p_row17_traceSegment_019_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 992 10 10, g32p_row17_traceSegment_019_0992_0010, g32p_row17_traceSegment_019_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 972 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 972 20 20, g32p_row17_traceSegment_019_0972_0020, g32p_row17_traceSegment_019_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1012 10 10, g32p_row17_traceSegment_019_1012_0010, g32p_row17_traceSegment_019_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1032 10 11, g32p_row17_traceSegment_019_1032_0010, g32p_row17_traceSegment_019_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1012 20 21, g32p_row17_traceSegment_019_1012_0020, g32p_row17_traceSegment_019_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 972 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 972 40 41, g32p_row17_traceSegment_019_0972_0040, g32p_row17_traceSegment_019_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1053 10 10, g32p_row17_traceSegment_019_1053_0010, g32p_row17_traceSegment_019_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1073 10 10, g32p_row17_traceSegment_019_1073_0010, g32p_row17_traceSegment_019_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1053 20 20, g32p_row17_traceSegment_019_1053_0020, g32p_row17_traceSegment_019_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1093 10 10, g32p_row17_traceSegment_019_1093_0010, g32p_row17_traceSegment_019_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1113 10 11, g32p_row17_traceSegment_019_1113_0010, g32p_row17_traceSegment_019_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1093 20 21, g32p_row17_traceSegment_019_1093_0020, g32p_row17_traceSegment_019_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1053 40 41, g32p_row17_traceSegment_019_1053_0040, g32p_row17_traceSegment_019_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_019 972 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 972 81 81, g32p_row17_traceSegment_019_0972_0081, g32p_row17_traceSegment_019_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1134 10 10, g32p_row17_traceSegment_019_1134_0010, g32p_row17_traceSegment_019_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1154 10 10, g32p_row17_traceSegment_019_1154_0010, g32p_row17_traceSegment_019_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1134 20 20, g32p_row17_traceSegment_019_1134_0020, g32p_row17_traceSegment_019_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1174 10 10, g32p_row17_traceSegment_019_1174_0010, g32p_row17_traceSegment_019_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1194 10 11, g32p_row17_traceSegment_019_1194_0010, g32p_row17_traceSegment_019_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1174 20 21, g32p_row17_traceSegment_019_1174_0020, g32p_row17_traceSegment_019_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1134 40 41, g32p_row17_traceSegment_019_1134_0040, g32p_row17_traceSegment_019_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1215 10 10, g32p_row17_traceSegment_019_1215_0010, g32p_row17_traceSegment_019_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1235 10 10, g32p_row17_traceSegment_019_1235_0010, g32p_row17_traceSegment_019_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_019 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1215 20 20, g32p_row17_traceSegment_019_1215_0020, g32p_row17_traceSegment_019_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_019 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1255 10 10, g32p_row17_traceSegment_019_1255_0010, g32p_row17_traceSegment_019_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_019 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_019 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_019_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_019 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1275 10 11, g32p_row17_traceSegment_019_1275_0010, g32p_row17_traceSegment_019_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_019 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1255 20 21, g32p_row17_traceSegment_019_1255_0020, g32p_row17_traceSegment_019_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_019 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1215 40 41, g32p_row17_traceSegment_019_1215_0040, g32p_row17_traceSegment_019_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_019_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_019 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 1134 81 81, g32p_row17_traceSegment_019_1134_0081, g32p_row17_traceSegment_019_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_019 972 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 972 162 162, g32p_row17_traceSegment_019_0972_0162, g32p_row17_traceSegment_019_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_019 648 648 = [6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 648 324 324, g32p_row17_traceSegment_019_0648_0324, g32p_row17_traceSegment_019_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_019_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_019 0 1296 = [12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_019 0 648 648, g32p_row17_traceSegment_019_0000_0648, g32p_row17_traceSegment_019_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 19 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_019_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_021 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 21 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_021_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 0 10 10, g32p_row17_traceSegment_021_0000_0010, g32p_row17_traceSegment_021_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 20 10 = [2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 30 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 20 20 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 20 10 10, g32p_row17_traceSegment_021_0020_0010, g32p_row17_traceSegment_021_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 0 40 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 0 20 20, g32p_row17_traceSegment_021_0000_0020, g32p_row17_traceSegment_021_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 40 10 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 40 20 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 40 10 10, g32p_row17_traceSegment_021_0040_0010, g32p_row17_traceSegment_021_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 60 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 70 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 60 21 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 60 10 11, g32p_row17_traceSegment_021_0060_0010, g32p_row17_traceSegment_021_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 40 41 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 40 20 21, g32p_row17_traceSegment_021_0040_0020, g32p_row17_traceSegment_021_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 0 81 = [4, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 0 40 41, g32p_row17_traceSegment_021_0000_0040, g32p_row17_traceSegment_021_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 91 10 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 81 20 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 81 10 10, g32p_row17_traceSegment_021_0081_0010, g32p_row17_traceSegment_021_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 101 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 101 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 101 10 10, g32p_row17_traceSegment_021_0101_0010, g32p_row17_traceSegment_021_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 81 40 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 81 20 20, g32p_row17_traceSegment_021_0081_0020, g32p_row17_traceSegment_021_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 121 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 131 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 121 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 121 10 10, g32p_row17_traceSegment_021_0121_0010, g32p_row17_traceSegment_021_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 141 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 151 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 141 21 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 141 10 11, g32p_row17_traceSegment_021_0141_0010, g32p_row17_traceSegment_021_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 121 41 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 121 20 21, g32p_row17_traceSegment_021_0121_0020, g32p_row17_traceSegment_021_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 81 81 = [2, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 81 40 41, g32p_row17_traceSegment_021_0081_0040, g32p_row17_traceSegment_021_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_021 0 162 = [6, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 0 81 81, g32p_row17_traceSegment_021_0000_0081, g32p_row17_traceSegment_021_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 162 10 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 172 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 162 20 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 162 10 10, g32p_row17_traceSegment_021_0162_0010, g32p_row17_traceSegment_021_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 182 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 192 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 182 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 182 10 10, g32p_row17_traceSegment_021_0182_0010, g32p_row17_traceSegment_021_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 162 40 = [1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 162 20 20, g32p_row17_traceSegment_021_0162_0020, g32p_row17_traceSegment_021_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 202 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 212 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 202 20 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 202 10 10, g32p_row17_traceSegment_021_0202_0010, g32p_row17_traceSegment_021_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 222 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 222 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 222 10 11, g32p_row17_traceSegment_021_0222_0010, g32p_row17_traceSegment_021_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 202 41 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 202 20 21, g32p_row17_traceSegment_021_0202_0020, g32p_row17_traceSegment_021_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 162 81 = [1, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 162 40 41, g32p_row17_traceSegment_021_0162_0040, g32p_row17_traceSegment_021_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 243 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 253 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 243 20 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 243 10 10, g32p_row17_traceSegment_021_0243_0010, g32p_row17_traceSegment_021_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 263 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 273 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 263 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 263 10 10, g32p_row17_traceSegment_021_0263_0010, g32p_row17_traceSegment_021_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 243 40 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 243 20 20, g32p_row17_traceSegment_021_0243_0020, g32p_row17_traceSegment_021_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 283 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 293 10 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 283 20 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 283 10 10, g32p_row17_traceSegment_021_0283_0010, g32p_row17_traceSegment_021_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 313 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 303 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 303 10 11, g32p_row17_traceSegment_021_0303_0010, g32p_row17_traceSegment_021_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 283 41 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 283 20 21, g32p_row17_traceSegment_021_0283_0020, g32p_row17_traceSegment_021_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 243 81 = [2, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 243 40 41, g32p_row17_traceSegment_021_0243_0040, g32p_row17_traceSegment_021_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_021 162 162 = [3, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 162 81 81, g32p_row17_traceSegment_021_0162_0081, g32p_row17_traceSegment_021_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_021 0 324 = [9, 0, 0, 27] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 0 162 162, g32p_row17_traceSegment_021_0000_0162, g32p_row17_traceSegment_021_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 324 10 10, g32p_row17_traceSegment_021_0324_0010, g32p_row17_traceSegment_021_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 354 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 344 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 344 10 10, g32p_row17_traceSegment_021_0344_0010, g32p_row17_traceSegment_021_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 324 40 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 324 20 20, g32p_row17_traceSegment_021_0324_0020, g32p_row17_traceSegment_021_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 364 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 374 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 364 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 364 10 10, g32p_row17_traceSegment_021_0364_0010, g32p_row17_traceSegment_021_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 384 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 394 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 384 21 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 384 10 11, g32p_row17_traceSegment_021_0384_0010, g32p_row17_traceSegment_021_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 364 41 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 364 20 21, g32p_row17_traceSegment_021_0364_0020, g32p_row17_traceSegment_021_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 324 81 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 324 40 41, g32p_row17_traceSegment_021_0324_0040, g32p_row17_traceSegment_021_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 405 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 405 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 405 10 10, g32p_row17_traceSegment_021_0405_0010, g32p_row17_traceSegment_021_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 425 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 435 10 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 425 20 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 425 10 10, g32p_row17_traceSegment_021_0425_0010, g32p_row17_traceSegment_021_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 405 40 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 405 20 20, g32p_row17_traceSegment_021_0405_0020, g32p_row17_traceSegment_021_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 455 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 445 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 445 10 10, g32p_row17_traceSegment_021_0445_0010, g32p_row17_traceSegment_021_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 465 10 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 475 11 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 465 21 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 465 10 11, g32p_row17_traceSegment_021_0465_0010, g32p_row17_traceSegment_021_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 445 41 = [1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 445 20 21, g32p_row17_traceSegment_021_0445_0020, g32p_row17_traceSegment_021_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 405 81 = [3, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 405 40 41, g32p_row17_traceSegment_021_0405_0040, g32p_row17_traceSegment_021_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_021 324 162 = [3, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 324 81 81, g32p_row17_traceSegment_021_0324_0081, g32p_row17_traceSegment_021_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 486 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 496 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 486 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 486 10 10, g32p_row17_traceSegment_021_0486_0010, g32p_row17_traceSegment_021_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 506 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 516 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 506 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 506 10 10, g32p_row17_traceSegment_021_0506_0010, g32p_row17_traceSegment_021_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 486 40 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 486 20 20, g32p_row17_traceSegment_021_0486_0020, g32p_row17_traceSegment_021_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 526 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 526 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 526 10 10, g32p_row17_traceSegment_021_0526_0010, g32p_row17_traceSegment_021_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 546 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 546 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 546 10 11, g32p_row17_traceSegment_021_0546_0010, g32p_row17_traceSegment_021_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 526 41 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 526 20 21, g32p_row17_traceSegment_021_0526_0020, g32p_row17_traceSegment_021_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 486 81 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 486 40 41, g32p_row17_traceSegment_021_0486_0040, g32p_row17_traceSegment_021_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 567 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 567 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 567 10 10, g32p_row17_traceSegment_021_0567_0010, g32p_row17_traceSegment_021_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 597 10 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 587 20 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 587 10 10, g32p_row17_traceSegment_021_0587_0010, g32p_row17_traceSegment_021_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 567 40 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 567 20 20, g32p_row17_traceSegment_021_0567_0020, g32p_row17_traceSegment_021_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 607 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 607 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 607 10 10, g32p_row17_traceSegment_021_0607_0010, g32p_row17_traceSegment_021_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 627 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 627 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 627 10 11, g32p_row17_traceSegment_021_0627_0010, g32p_row17_traceSegment_021_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 607 41 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 607 20 21, g32p_row17_traceSegment_021_0607_0020, g32p_row17_traceSegment_021_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 567 81 = [1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 567 40 41, g32p_row17_traceSegment_021_0567_0040, g32p_row17_traceSegment_021_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_021 486 162 = [1, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 486 81 81, g32p_row17_traceSegment_021_0486_0081, g32p_row17_traceSegment_021_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_021 324 324 = [4, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 324 162 162, g32p_row17_traceSegment_021_0324_0162, g32p_row17_traceSegment_021_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_021 0 648 = [13, 0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 0 324 324, g32p_row17_traceSegment_021_0000_0324, g32p_row17_traceSegment_021_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 648 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 658 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 648 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 648 10 10, g32p_row17_traceSegment_021_0648_0010, g32p_row17_traceSegment_021_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 668 10 10, g32p_row17_traceSegment_021_0668_0010, g32p_row17_traceSegment_021_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 648 40 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 648 20 20, g32p_row17_traceSegment_021_0648_0020, g32p_row17_traceSegment_021_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 688 10 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 698 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 688 20 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 688 10 10, g32p_row17_traceSegment_021_0688_0010, g32p_row17_traceSegment_021_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 708 10 11, g32p_row17_traceSegment_021_0708_0010, g32p_row17_traceSegment_021_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 688 41 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 688 20 21, g32p_row17_traceSegment_021_0688_0020, g32p_row17_traceSegment_021_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 648 81 = [1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 648 40 41, g32p_row17_traceSegment_021_0648_0040, g32p_row17_traceSegment_021_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 729 10 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 739 10 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 729 20 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 729 10 10, g32p_row17_traceSegment_021_0729_0010, g32p_row17_traceSegment_021_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 749 10 10, g32p_row17_traceSegment_021_0749_0010, g32p_row17_traceSegment_021_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 729 40 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 729 20 20, g32p_row17_traceSegment_021_0729_0020, g32p_row17_traceSegment_021_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 769 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 769 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 769 10 10, g32p_row17_traceSegment_021_0769_0010, g32p_row17_traceSegment_021_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 789 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 799 11 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 789 21 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 789 10 11, g32p_row17_traceSegment_021_0789_0010, g32p_row17_traceSegment_021_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 769 41 = [1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 769 20 21, g32p_row17_traceSegment_021_0769_0020, g32p_row17_traceSegment_021_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 729 81 = [3, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 729 40 41, g32p_row17_traceSegment_021_0729_0040, g32p_row17_traceSegment_021_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_021 648 162 = [4, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 648 81 81, g32p_row17_traceSegment_021_0648_0081, g32p_row17_traceSegment_021_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 810 10 10, g32p_row17_traceSegment_021_0810_0010, g32p_row17_traceSegment_021_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 840 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 830 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 830 10 10, g32p_row17_traceSegment_021_0830_0010, g32p_row17_traceSegment_021_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 810 40 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 810 20 20, g32p_row17_traceSegment_021_0810_0020, g32p_row17_traceSegment_021_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 850 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 850 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 850 10 10, g32p_row17_traceSegment_021_0850_0010, g32p_row17_traceSegment_021_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 870 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 870 21 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 870 10 11, g32p_row17_traceSegment_021_0870_0010, g32p_row17_traceSegment_021_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 850 41 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 850 20 21, g32p_row17_traceSegment_021_0850_0020, g32p_row17_traceSegment_021_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 810 81 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 810 40 41, g32p_row17_traceSegment_021_0810_0040, g32p_row17_traceSegment_021_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 901 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 891 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 891 10 10, g32p_row17_traceSegment_021_0891_0010, g32p_row17_traceSegment_021_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 911 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 911 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 911 10 10, g32p_row17_traceSegment_021_0911_0010, g32p_row17_traceSegment_021_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 891 40 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 891 20 20, g32p_row17_traceSegment_021_0891_0020, g32p_row17_traceSegment_021_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 931 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 931 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 931 10 10, g32p_row17_traceSegment_021_0931_0010, g32p_row17_traceSegment_021_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 951 10 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 951 21 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 951 10 11, g32p_row17_traceSegment_021_0951_0010, g32p_row17_traceSegment_021_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 931 41 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 931 20 21, g32p_row17_traceSegment_021_0931_0020, g32p_row17_traceSegment_021_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 891 81 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 891 40 41, g32p_row17_traceSegment_021_0891_0040, g32p_row17_traceSegment_021_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_021 810 162 = [5, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 810 81 81, g32p_row17_traceSegment_021_0810_0081, g32p_row17_traceSegment_021_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_021 648 324 = [9, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 648 162 162, g32p_row17_traceSegment_021_0648_0162, g32p_row17_traceSegment_021_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 972 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 982 10 = [2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 972 20 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 972 10 10, g32p_row17_traceSegment_021_0972_0010, g32p_row17_traceSegment_021_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 992 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1002 10 = [2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 992 20 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 992 10 10, g32p_row17_traceSegment_021_0992_0010, g32p_row17_traceSegment_021_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 972 40 = [4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 972 20 20, g32p_row17_traceSegment_021_0972_0020, g32p_row17_traceSegment_021_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1012 10 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1022 10 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 1012 20 = [3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1012 10 10, g32p_row17_traceSegment_021_1012_0010, g32p_row17_traceSegment_021_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1032 10 11, g32p_row17_traceSegment_021_1032_0010, g32p_row17_traceSegment_021_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 1012 41 = [3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1012 20 21, g32p_row17_traceSegment_021_1012_0020, g32p_row17_traceSegment_021_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 972 81 = [7, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 972 40 41, g32p_row17_traceSegment_021_0972_0040, g32p_row17_traceSegment_021_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1053 10 10, g32p_row17_traceSegment_021_1053_0010, g32p_row17_traceSegment_021_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1083 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 1073 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1073 10 10, g32p_row17_traceSegment_021_1073_0010, g32p_row17_traceSegment_021_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 1053 40 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1053 20 20, g32p_row17_traceSegment_021_1053_0020, g32p_row17_traceSegment_021_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1093 10 10, g32p_row17_traceSegment_021_1093_0010, g32p_row17_traceSegment_021_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1113 10 11, g32p_row17_traceSegment_021_1113_0010, g32p_row17_traceSegment_021_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1093 20 21, g32p_row17_traceSegment_021_1093_0020, g32p_row17_traceSegment_021_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 1053 81 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1053 40 41, g32p_row17_traceSegment_021_1053_0040, g32p_row17_traceSegment_021_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_021 972 162 = [7, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 972 81 81, g32p_row17_traceSegment_021_0972_0081, g32p_row17_traceSegment_021_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1144 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 1134 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1134 10 10, g32p_row17_traceSegment_021_1134_0010, g32p_row17_traceSegment_021_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1154 10 10, g32p_row17_traceSegment_021_1154_0010, g32p_row17_traceSegment_021_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 1134 40 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1134 20 20, g32p_row17_traceSegment_021_1134_0020, g32p_row17_traceSegment_021_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1174 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1184 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 1174 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1174 10 10, g32p_row17_traceSegment_021_1174_0010, g32p_row17_traceSegment_021_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1194 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 1204 11 = [3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 1194 21 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1194 10 11, g32p_row17_traceSegment_021_1194_0010, g32p_row17_traceSegment_021_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 1174 41 = [6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1174 20 21, g32p_row17_traceSegment_021_1174_0020, g32p_row17_traceSegment_021_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 1134 81 = [6, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1134 40 41, g32p_row17_traceSegment_021_1134_0040, g32p_row17_traceSegment_021_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1215 10 10, g32p_row17_traceSegment_021_1215_0010, g32p_row17_traceSegment_021_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1245 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 1235 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1235 10 10, g32p_row17_traceSegment_021_1235_0010, g32p_row17_traceSegment_021_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_021 1215 40 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1215 20 20, g32p_row17_traceSegment_021_1215_0020, g32p_row17_traceSegment_021_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1255 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_021 1255 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1255 10 10, g32p_row17_traceSegment_021_1255_0010, g32p_row17_traceSegment_021_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_021 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_021 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_021_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_021 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1275 10 11, g32p_row17_traceSegment_021_1275_0010, g32p_row17_traceSegment_021_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_021 1255 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1255 20 21, g32p_row17_traceSegment_021_1255_0020, g32p_row17_traceSegment_021_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_021 1215 81 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1215 40 41, g32p_row17_traceSegment_021_1215_0040, g32p_row17_traceSegment_021_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_021_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_021 1134 162 = [7, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 1134 81 81, g32p_row17_traceSegment_021_1134_0081, g32p_row17_traceSegment_021_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_021 972 324 = [14, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 972 162 162, g32p_row17_traceSegment_021_0972_0162, g32p_row17_traceSegment_021_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_021 648 648 = [23, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 648 324 324, g32p_row17_traceSegment_021_0648_0324, g32p_row17_traceSegment_021_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_021_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_021 0 1296 = [36, 0, 0, 72] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_021 0 648 648, g32p_row17_traceSegment_021_0000_0648, g32p_row17_traceSegment_021_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_021 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 21 = [36, 0, 0, 72] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_021_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_023 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 23 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_023_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 0 10 10, g32p_row17_traceSegment_023_0000_0010, g32p_row17_traceSegment_023_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 20 10 10, g32p_row17_traceSegment_023_0020_0010, g32p_row17_traceSegment_023_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 0 20 20, g32p_row17_traceSegment_023_0000_0020, g32p_row17_traceSegment_023_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 40 10 10, g32p_row17_traceSegment_023_0040_0010, g32p_row17_traceSegment_023_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 60 10 11, g32p_row17_traceSegment_023_0060_0010, g32p_row17_traceSegment_023_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 40 20 21, g32p_row17_traceSegment_023_0040_0020, g32p_row17_traceSegment_023_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 0 40 41, g32p_row17_traceSegment_023_0000_0040, g32p_row17_traceSegment_023_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 81 10 10, g32p_row17_traceSegment_023_0081_0010, g32p_row17_traceSegment_023_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 101 10 10, g32p_row17_traceSegment_023_0101_0010, g32p_row17_traceSegment_023_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 81 20 20, g32p_row17_traceSegment_023_0081_0020, g32p_row17_traceSegment_023_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 131 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 121 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 121 10 10, g32p_row17_traceSegment_023_0121_0010, g32p_row17_traceSegment_023_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 141 10 11, g32p_row17_traceSegment_023_0141_0010, g32p_row17_traceSegment_023_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 121 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 121 20 21, g32p_row17_traceSegment_023_0121_0020, g32p_row17_traceSegment_023_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 81 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 81 40 41, g32p_row17_traceSegment_023_0081_0040, g32p_row17_traceSegment_023_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_023 0 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 0 81 81, g32p_row17_traceSegment_023_0000_0081, g32p_row17_traceSegment_023_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 162 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 172 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 162 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 162 10 10, g32p_row17_traceSegment_023_0162_0010, g32p_row17_traceSegment_023_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 182 10 10, g32p_row17_traceSegment_023_0182_0010, g32p_row17_traceSegment_023_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 162 40 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 162 20 20, g32p_row17_traceSegment_023_0162_0020, g32p_row17_traceSegment_023_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 202 10 10, g32p_row17_traceSegment_023_0202_0010, g32p_row17_traceSegment_023_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 222 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 222 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 222 10 11, g32p_row17_traceSegment_023_0222_0010, g32p_row17_traceSegment_023_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 202 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 202 20 21, g32p_row17_traceSegment_023_0202_0020, g32p_row17_traceSegment_023_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 162 81 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 162 40 41, g32p_row17_traceSegment_023_0162_0040, g32p_row17_traceSegment_023_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 243 10 10, g32p_row17_traceSegment_023_0243_0010, g32p_row17_traceSegment_023_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 263 10 10, g32p_row17_traceSegment_023_0263_0010, g32p_row17_traceSegment_023_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 243 20 20, g32p_row17_traceSegment_023_0243_0020, g32p_row17_traceSegment_023_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 283 10 10, g32p_row17_traceSegment_023_0283_0010, g32p_row17_traceSegment_023_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 313 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 303 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 303 10 11, g32p_row17_traceSegment_023_0303_0010, g32p_row17_traceSegment_023_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 283 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 283 20 21, g32p_row17_traceSegment_023_0283_0020, g32p_row17_traceSegment_023_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 243 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 243 40 41, g32p_row17_traceSegment_023_0243_0040, g32p_row17_traceSegment_023_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_023 162 162 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 162 81 81, g32p_row17_traceSegment_023_0162_0081, g32p_row17_traceSegment_023_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_023 0 324 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 0 162 162, g32p_row17_traceSegment_023_0000_0162, g32p_row17_traceSegment_023_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 324 10 10, g32p_row17_traceSegment_023_0324_0010, g32p_row17_traceSegment_023_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 354 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 344 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 344 10 10, g32p_row17_traceSegment_023_0344_0010, g32p_row17_traceSegment_023_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 324 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 324 20 20, g32p_row17_traceSegment_023_0324_0020, g32p_row17_traceSegment_023_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 364 10 10, g32p_row17_traceSegment_023_0364_0010, g32p_row17_traceSegment_023_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 384 10 11, g32p_row17_traceSegment_023_0384_0010, g32p_row17_traceSegment_023_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 364 20 21, g32p_row17_traceSegment_023_0364_0020, g32p_row17_traceSegment_023_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 324 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 324 40 41, g32p_row17_traceSegment_023_0324_0040, g32p_row17_traceSegment_023_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 405 10 10, g32p_row17_traceSegment_023_0405_0010, g32p_row17_traceSegment_023_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 425 10 10, g32p_row17_traceSegment_023_0425_0010, g32p_row17_traceSegment_023_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 405 20 20, g32p_row17_traceSegment_023_0405_0020, g32p_row17_traceSegment_023_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 445 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 445 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 445 10 10, g32p_row17_traceSegment_023_0445_0010, g32p_row17_traceSegment_023_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 465 10 11, g32p_row17_traceSegment_023_0465_0010, g32p_row17_traceSegment_023_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 445 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 445 20 21, g32p_row17_traceSegment_023_0445_0020, g32p_row17_traceSegment_023_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 405 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 405 40 41, g32p_row17_traceSegment_023_0405_0040, g32p_row17_traceSegment_023_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_023 324 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 324 81 81, g32p_row17_traceSegment_023_0324_0081, g32p_row17_traceSegment_023_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 486 10 10, g32p_row17_traceSegment_023_0486_0010, g32p_row17_traceSegment_023_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 506 10 10, g32p_row17_traceSegment_023_0506_0010, g32p_row17_traceSegment_023_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 486 20 20, g32p_row17_traceSegment_023_0486_0020, g32p_row17_traceSegment_023_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 526 10 10, g32p_row17_traceSegment_023_0526_0010, g32p_row17_traceSegment_023_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 546 10 11, g32p_row17_traceSegment_023_0546_0010, g32p_row17_traceSegment_023_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 526 20 21, g32p_row17_traceSegment_023_0526_0020, g32p_row17_traceSegment_023_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 486 40 41, g32p_row17_traceSegment_023_0486_0040, g32p_row17_traceSegment_023_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 567 10 10, g32p_row17_traceSegment_023_0567_0010, g32p_row17_traceSegment_023_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 587 10 10, g32p_row17_traceSegment_023_0587_0010, g32p_row17_traceSegment_023_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 567 20 20, g32p_row17_traceSegment_023_0567_0020, g32p_row17_traceSegment_023_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 607 10 10, g32p_row17_traceSegment_023_0607_0010, g32p_row17_traceSegment_023_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 627 10 11, g32p_row17_traceSegment_023_0627_0010, g32p_row17_traceSegment_023_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 607 20 21, g32p_row17_traceSegment_023_0607_0020, g32p_row17_traceSegment_023_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 567 40 41, g32p_row17_traceSegment_023_0567_0040, g32p_row17_traceSegment_023_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_023 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 486 81 81, g32p_row17_traceSegment_023_0486_0081, g32p_row17_traceSegment_023_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_023 324 324 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 324 162 162, g32p_row17_traceSegment_023_0324_0162, g32p_row17_traceSegment_023_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_023 0 648 = [7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 0 324 324, g32p_row17_traceSegment_023_0000_0324, g32p_row17_traceSegment_023_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 648 10 10, g32p_row17_traceSegment_023_0648_0010, g32p_row17_traceSegment_023_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 668 10 10, g32p_row17_traceSegment_023_0668_0010, g32p_row17_traceSegment_023_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 648 20 20, g32p_row17_traceSegment_023_0648_0020, g32p_row17_traceSegment_023_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 688 10 10, g32p_row17_traceSegment_023_0688_0010, g32p_row17_traceSegment_023_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 708 10 11, g32p_row17_traceSegment_023_0708_0010, g32p_row17_traceSegment_023_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 688 20 21, g32p_row17_traceSegment_023_0688_0020, g32p_row17_traceSegment_023_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 648 40 41, g32p_row17_traceSegment_023_0648_0040, g32p_row17_traceSegment_023_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 729 10 10, g32p_row17_traceSegment_023_0729_0010, g32p_row17_traceSegment_023_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 759 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 749 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 749 10 10, g32p_row17_traceSegment_023_0749_0010, g32p_row17_traceSegment_023_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 729 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 729 20 20, g32p_row17_traceSegment_023_0729_0020, g32p_row17_traceSegment_023_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 779 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 769 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 769 10 10, g32p_row17_traceSegment_023_0769_0010, g32p_row17_traceSegment_023_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 789 10 11, g32p_row17_traceSegment_023_0789_0010, g32p_row17_traceSegment_023_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 769 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 769 20 21, g32p_row17_traceSegment_023_0769_0020, g32p_row17_traceSegment_023_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 729 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 729 40 41, g32p_row17_traceSegment_023_0729_0040, g32p_row17_traceSegment_023_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_023 648 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 648 81 81, g32p_row17_traceSegment_023_0648_0081, g32p_row17_traceSegment_023_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 810 10 10, g32p_row17_traceSegment_023_0810_0010, g32p_row17_traceSegment_023_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 830 10 10, g32p_row17_traceSegment_023_0830_0010, g32p_row17_traceSegment_023_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 810 20 20, g32p_row17_traceSegment_023_0810_0020, g32p_row17_traceSegment_023_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 850 10 10, g32p_row17_traceSegment_023_0850_0010, g32p_row17_traceSegment_023_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 870 10 11, g32p_row17_traceSegment_023_0870_0010, g32p_row17_traceSegment_023_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 850 20 21, g32p_row17_traceSegment_023_0850_0020, g32p_row17_traceSegment_023_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 810 40 41, g32p_row17_traceSegment_023_0810_0040, g32p_row17_traceSegment_023_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 891 10 10, g32p_row17_traceSegment_023_0891_0010, g32p_row17_traceSegment_023_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 911 10 10, g32p_row17_traceSegment_023_0911_0010, g32p_row17_traceSegment_023_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 891 20 20, g32p_row17_traceSegment_023_0891_0020, g32p_row17_traceSegment_023_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 931 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 931 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 931 10 10, g32p_row17_traceSegment_023_0931_0010, g32p_row17_traceSegment_023_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 961 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 951 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 951 10 11, g32p_row17_traceSegment_023_0951_0010, g32p_row17_traceSegment_023_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 931 41 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 931 20 21, g32p_row17_traceSegment_023_0931_0020, g32p_row17_traceSegment_023_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 891 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 891 40 41, g32p_row17_traceSegment_023_0891_0040, g32p_row17_traceSegment_023_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_023 810 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 810 81 81, g32p_row17_traceSegment_023_0810_0081, g32p_row17_traceSegment_023_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_023 648 324 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 648 162 162, g32p_row17_traceSegment_023_0648_0162, g32p_row17_traceSegment_023_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 972 10 10, g32p_row17_traceSegment_023_0972_0010, g32p_row17_traceSegment_023_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 992 10 10, g32p_row17_traceSegment_023_0992_0010, g32p_row17_traceSegment_023_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 972 20 20, g32p_row17_traceSegment_023_0972_0020, g32p_row17_traceSegment_023_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1012 10 10, g32p_row17_traceSegment_023_1012_0010, g32p_row17_traceSegment_023_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1032 10 11, g32p_row17_traceSegment_023_1032_0010, g32p_row17_traceSegment_023_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1012 20 21, g32p_row17_traceSegment_023_1012_0020, g32p_row17_traceSegment_023_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 972 40 41, g32p_row17_traceSegment_023_0972_0040, g32p_row17_traceSegment_023_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1053 10 10, g32p_row17_traceSegment_023_1053_0010, g32p_row17_traceSegment_023_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1073 10 10, g32p_row17_traceSegment_023_1073_0010, g32p_row17_traceSegment_023_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1053 20 20, g32p_row17_traceSegment_023_1053_0020, g32p_row17_traceSegment_023_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1103 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 1093 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1093 10 10, g32p_row17_traceSegment_023_1093_0010, g32p_row17_traceSegment_023_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1113 10 11, g32p_row17_traceSegment_023_1113_0010, g32p_row17_traceSegment_023_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 1093 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1093 20 21, g32p_row17_traceSegment_023_1093_0020, g32p_row17_traceSegment_023_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 1053 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1053 40 41, g32p_row17_traceSegment_023_1053_0040, g32p_row17_traceSegment_023_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_023 972 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 972 81 81, g32p_row17_traceSegment_023_0972_0081, g32p_row17_traceSegment_023_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1134 10 10, g32p_row17_traceSegment_023_1134_0010, g32p_row17_traceSegment_023_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1154 10 10, g32p_row17_traceSegment_023_1154_0010, g32p_row17_traceSegment_023_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1134 20 20, g32p_row17_traceSegment_023_1134_0020, g32p_row17_traceSegment_023_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1174 10 10, g32p_row17_traceSegment_023_1174_0010, g32p_row17_traceSegment_023_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1194 10 11, g32p_row17_traceSegment_023_1194_0010, g32p_row17_traceSegment_023_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1174 20 21, g32p_row17_traceSegment_023_1174_0020, g32p_row17_traceSegment_023_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1134 40 41, g32p_row17_traceSegment_023_1134_0040, g32p_row17_traceSegment_023_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1215 10 10, g32p_row17_traceSegment_023_1215_0010, g32p_row17_traceSegment_023_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1235 10 10, g32p_row17_traceSegment_023_1235_0010, g32p_row17_traceSegment_023_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_023 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1215 20 20, g32p_row17_traceSegment_023_1215_0020, g32p_row17_traceSegment_023_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_023 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1255 10 10, g32p_row17_traceSegment_023_1255_0010, g32p_row17_traceSegment_023_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_023 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_023 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_023_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_023 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1275 10 11, g32p_row17_traceSegment_023_1275_0010, g32p_row17_traceSegment_023_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_023 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1255 20 21, g32p_row17_traceSegment_023_1255_0020, g32p_row17_traceSegment_023_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_023 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1215 40 41, g32p_row17_traceSegment_023_1215_0040, g32p_row17_traceSegment_023_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_023_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_023 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 1134 81 81, g32p_row17_traceSegment_023_1134_0081, g32p_row17_traceSegment_023_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_023 972 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 972 162 162, g32p_row17_traceSegment_023_0972_0162, g32p_row17_traceSegment_023_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_023 648 648 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 648 324 324, g32p_row17_traceSegment_023_0648_0324, g32p_row17_traceSegment_023_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_023_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_023 0 1296 = [12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_023 0 648 648, g32p_row17_traceSegment_023_0000_0648, g32p_row17_traceSegment_023_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 23 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_023_0000_1296

end HodgeLean.Foundations.Program

end
end
