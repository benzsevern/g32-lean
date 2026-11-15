import HodgeLean.Foundations.Program.G32PropFourSixPacked0367
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0368

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_024 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 24 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_024_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 0 10 10, g32p_row17_traceSegment_024_0000_0010, g32p_row17_traceSegment_024_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 20 10 10, g32p_row17_traceSegment_024_0020_0010, g32p_row17_traceSegment_024_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 0 20 20, g32p_row17_traceSegment_024_0000_0020, g32p_row17_traceSegment_024_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 40 10 10, g32p_row17_traceSegment_024_0040_0010, g32p_row17_traceSegment_024_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 60 10 11, g32p_row17_traceSegment_024_0060_0010, g32p_row17_traceSegment_024_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 40 20 21, g32p_row17_traceSegment_024_0040_0020, g32p_row17_traceSegment_024_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 0 40 41, g32p_row17_traceSegment_024_0000_0040, g32p_row17_traceSegment_024_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 81 10 10, g32p_row17_traceSegment_024_0081_0010, g32p_row17_traceSegment_024_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 101 10 10, g32p_row17_traceSegment_024_0101_0010, g32p_row17_traceSegment_024_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 81 20 20, g32p_row17_traceSegment_024_0081_0020, g32p_row17_traceSegment_024_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 121 10 10, g32p_row17_traceSegment_024_0121_0010, g32p_row17_traceSegment_024_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 141 10 11, g32p_row17_traceSegment_024_0141_0010, g32p_row17_traceSegment_024_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 121 20 21, g32p_row17_traceSegment_024_0121_0020, g32p_row17_traceSegment_024_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 81 40 41, g32p_row17_traceSegment_024_0081_0040, g32p_row17_traceSegment_024_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_024 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 0 81 81, g32p_row17_traceSegment_024_0000_0081, g32p_row17_traceSegment_024_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 162 10 10, g32p_row17_traceSegment_024_0162_0010, g32p_row17_traceSegment_024_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 182 10 10, g32p_row17_traceSegment_024_0182_0010, g32p_row17_traceSegment_024_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 162 20 20, g32p_row17_traceSegment_024_0162_0020, g32p_row17_traceSegment_024_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 202 10 10, g32p_row17_traceSegment_024_0202_0010, g32p_row17_traceSegment_024_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 222 10 11, g32p_row17_traceSegment_024_0222_0010, g32p_row17_traceSegment_024_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 202 20 21, g32p_row17_traceSegment_024_0202_0020, g32p_row17_traceSegment_024_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 162 40 41, g32p_row17_traceSegment_024_0162_0040, g32p_row17_traceSegment_024_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 243 10 10, g32p_row17_traceSegment_024_0243_0010, g32p_row17_traceSegment_024_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 263 10 10, g32p_row17_traceSegment_024_0263_0010, g32p_row17_traceSegment_024_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 243 20 20, g32p_row17_traceSegment_024_0243_0020, g32p_row17_traceSegment_024_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 283 10 10, g32p_row17_traceSegment_024_0283_0010, g32p_row17_traceSegment_024_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 303 10 11, g32p_row17_traceSegment_024_0303_0010, g32p_row17_traceSegment_024_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 283 20 21, g32p_row17_traceSegment_024_0283_0020, g32p_row17_traceSegment_024_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 243 40 41, g32p_row17_traceSegment_024_0243_0040, g32p_row17_traceSegment_024_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_024 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 162 81 81, g32p_row17_traceSegment_024_0162_0081, g32p_row17_traceSegment_024_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_024 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 0 162 162, g32p_row17_traceSegment_024_0000_0162, g32p_row17_traceSegment_024_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 324 10 10, g32p_row17_traceSegment_024_0324_0010, g32p_row17_traceSegment_024_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 344 10 10, g32p_row17_traceSegment_024_0344_0010, g32p_row17_traceSegment_024_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 324 20 20, g32p_row17_traceSegment_024_0324_0020, g32p_row17_traceSegment_024_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 364 10 10, g32p_row17_traceSegment_024_0364_0010, g32p_row17_traceSegment_024_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 384 10 11, g32p_row17_traceSegment_024_0384_0010, g32p_row17_traceSegment_024_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 364 20 21, g32p_row17_traceSegment_024_0364_0020, g32p_row17_traceSegment_024_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 324 40 41, g32p_row17_traceSegment_024_0324_0040, g32p_row17_traceSegment_024_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 405 10 10, g32p_row17_traceSegment_024_0405_0010, g32p_row17_traceSegment_024_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 425 10 10, g32p_row17_traceSegment_024_0425_0010, g32p_row17_traceSegment_024_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 405 20 20, g32p_row17_traceSegment_024_0405_0020, g32p_row17_traceSegment_024_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 445 10 10, g32p_row17_traceSegment_024_0445_0010, g32p_row17_traceSegment_024_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 465 10 11, g32p_row17_traceSegment_024_0465_0010, g32p_row17_traceSegment_024_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 445 20 21, g32p_row17_traceSegment_024_0445_0020, g32p_row17_traceSegment_024_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 405 40 41, g32p_row17_traceSegment_024_0405_0040, g32p_row17_traceSegment_024_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_024 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 324 81 81, g32p_row17_traceSegment_024_0324_0081, g32p_row17_traceSegment_024_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 486 10 10, g32p_row17_traceSegment_024_0486_0010, g32p_row17_traceSegment_024_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 506 10 10, g32p_row17_traceSegment_024_0506_0010, g32p_row17_traceSegment_024_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 486 20 20, g32p_row17_traceSegment_024_0486_0020, g32p_row17_traceSegment_024_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 526 10 10, g32p_row17_traceSegment_024_0526_0010, g32p_row17_traceSegment_024_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 546 10 11, g32p_row17_traceSegment_024_0546_0010, g32p_row17_traceSegment_024_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 526 20 21, g32p_row17_traceSegment_024_0526_0020, g32p_row17_traceSegment_024_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 486 40 41, g32p_row17_traceSegment_024_0486_0040, g32p_row17_traceSegment_024_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 577 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 567 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 567 10 10, g32p_row17_traceSegment_024_0567_0010, g32p_row17_traceSegment_024_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 587 10 10, g32p_row17_traceSegment_024_0587_0010, g32p_row17_traceSegment_024_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 567 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 567 20 20, g32p_row17_traceSegment_024_0567_0020, g32p_row17_traceSegment_024_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 607 10 10, g32p_row17_traceSegment_024_0607_0010, g32p_row17_traceSegment_024_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 627 10 11, g32p_row17_traceSegment_024_0627_0010, g32p_row17_traceSegment_024_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 607 20 21, g32p_row17_traceSegment_024_0607_0020, g32p_row17_traceSegment_024_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 567 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 567 40 41, g32p_row17_traceSegment_024_0567_0040, g32p_row17_traceSegment_024_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_024 486 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 486 81 81, g32p_row17_traceSegment_024_0486_0081, g32p_row17_traceSegment_024_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_024 324 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 324 162 162, g32p_row17_traceSegment_024_0324_0162, g32p_row17_traceSegment_024_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_024 0 648 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 0 324 324, g32p_row17_traceSegment_024_0000_0324, g32p_row17_traceSegment_024_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 648 10 10, g32p_row17_traceSegment_024_0648_0010, g32p_row17_traceSegment_024_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 668 10 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 678 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 668 20 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 668 10 10, g32p_row17_traceSegment_024_0668_0010, g32p_row17_traceSegment_024_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 648 40 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 648 20 20, g32p_row17_traceSegment_024_0648_0020, g32p_row17_traceSegment_024_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 688 10 10, g32p_row17_traceSegment_024_0688_0010, g32p_row17_traceSegment_024_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 708 10 11, g32p_row17_traceSegment_024_0708_0010, g32p_row17_traceSegment_024_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 688 20 21, g32p_row17_traceSegment_024_0688_0020, g32p_row17_traceSegment_024_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 648 81 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 648 40 41, g32p_row17_traceSegment_024_0648_0040, g32p_row17_traceSegment_024_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 729 10 10, g32p_row17_traceSegment_024_0729_0010, g32p_row17_traceSegment_024_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 759 10 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 749 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 749 10 10, g32p_row17_traceSegment_024_0749_0010, g32p_row17_traceSegment_024_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 729 40 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 729 20 20, g32p_row17_traceSegment_024_0729_0020, g32p_row17_traceSegment_024_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 769 10 10, g32p_row17_traceSegment_024_0769_0010, g32p_row17_traceSegment_024_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 789 10 11, g32p_row17_traceSegment_024_0789_0010, g32p_row17_traceSegment_024_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 769 20 21, g32p_row17_traceSegment_024_0769_0020, g32p_row17_traceSegment_024_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 729 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 729 40 41, g32p_row17_traceSegment_024_0729_0040, g32p_row17_traceSegment_024_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_024 648 162 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 648 81 81, g32p_row17_traceSegment_024_0648_0081, g32p_row17_traceSegment_024_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 810 10 10, g32p_row17_traceSegment_024_0810_0010, g32p_row17_traceSegment_024_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 830 10 10, g32p_row17_traceSegment_024_0830_0010, g32p_row17_traceSegment_024_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 810 20 20, g32p_row17_traceSegment_024_0810_0020, g32p_row17_traceSegment_024_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 850 10 10, g32p_row17_traceSegment_024_0850_0010, g32p_row17_traceSegment_024_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 870 10 11, g32p_row17_traceSegment_024_0870_0010, g32p_row17_traceSegment_024_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 850 20 21, g32p_row17_traceSegment_024_0850_0020, g32p_row17_traceSegment_024_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 810 40 41, g32p_row17_traceSegment_024_0810_0040, g32p_row17_traceSegment_024_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 891 10 10, g32p_row17_traceSegment_024_0891_0010, g32p_row17_traceSegment_024_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 911 10 10, g32p_row17_traceSegment_024_0911_0010, g32p_row17_traceSegment_024_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 891 20 20, g32p_row17_traceSegment_024_0891_0020, g32p_row17_traceSegment_024_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 931 10 10, g32p_row17_traceSegment_024_0931_0010, g32p_row17_traceSegment_024_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 951 10 11, g32p_row17_traceSegment_024_0951_0010, g32p_row17_traceSegment_024_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 931 20 21, g32p_row17_traceSegment_024_0931_0020, g32p_row17_traceSegment_024_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 891 40 41, g32p_row17_traceSegment_024_0891_0040, g32p_row17_traceSegment_024_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_024 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 810 81 81, g32p_row17_traceSegment_024_0810_0081, g32p_row17_traceSegment_024_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_024 648 324 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 648 162 162, g32p_row17_traceSegment_024_0648_0162, g32p_row17_traceSegment_024_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 972 10 10, g32p_row17_traceSegment_024_0972_0010, g32p_row17_traceSegment_024_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 992 10 10, g32p_row17_traceSegment_024_0992_0010, g32p_row17_traceSegment_024_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 972 20 20, g32p_row17_traceSegment_024_0972_0020, g32p_row17_traceSegment_024_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1012 10 10, g32p_row17_traceSegment_024_1012_0010, g32p_row17_traceSegment_024_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1032 10 11, g32p_row17_traceSegment_024_1032_0010, g32p_row17_traceSegment_024_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1012 20 21, g32p_row17_traceSegment_024_1012_0020, g32p_row17_traceSegment_024_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 972 40 41, g32p_row17_traceSegment_024_0972_0040, g32p_row17_traceSegment_024_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1053 10 10, g32p_row17_traceSegment_024_1053_0010, g32p_row17_traceSegment_024_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1073 10 10, g32p_row17_traceSegment_024_1073_0010, g32p_row17_traceSegment_024_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1053 20 20, g32p_row17_traceSegment_024_1053_0020, g32p_row17_traceSegment_024_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1093 10 10, g32p_row17_traceSegment_024_1093_0010, g32p_row17_traceSegment_024_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1113 10 11, g32p_row17_traceSegment_024_1113_0010, g32p_row17_traceSegment_024_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1093 20 21, g32p_row17_traceSegment_024_1093_0020, g32p_row17_traceSegment_024_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1053 40 41, g32p_row17_traceSegment_024_1053_0040, g32p_row17_traceSegment_024_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_024 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 972 81 81, g32p_row17_traceSegment_024_0972_0081, g32p_row17_traceSegment_024_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1134 10 10, g32p_row17_traceSegment_024_1134_0010, g32p_row17_traceSegment_024_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1154 10 10, g32p_row17_traceSegment_024_1154_0010, g32p_row17_traceSegment_024_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1134 20 20, g32p_row17_traceSegment_024_1134_0020, g32p_row17_traceSegment_024_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1174 10 10, g32p_row17_traceSegment_024_1174_0010, g32p_row17_traceSegment_024_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1194 10 11, g32p_row17_traceSegment_024_1194_0010, g32p_row17_traceSegment_024_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1174 20 21, g32p_row17_traceSegment_024_1174_0020, g32p_row17_traceSegment_024_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1134 40 41, g32p_row17_traceSegment_024_1134_0040, g32p_row17_traceSegment_024_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1215 10 10, g32p_row17_traceSegment_024_1215_0010, g32p_row17_traceSegment_024_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1235 10 10, g32p_row17_traceSegment_024_1235_0010, g32p_row17_traceSegment_024_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_024 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1215 20 20, g32p_row17_traceSegment_024_1215_0020, g32p_row17_traceSegment_024_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_024 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1255 10 10, g32p_row17_traceSegment_024_1255_0010, g32p_row17_traceSegment_024_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_024 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_024 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_024_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_024 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1275 10 11, g32p_row17_traceSegment_024_1275_0010, g32p_row17_traceSegment_024_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_024 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1255 20 21, g32p_row17_traceSegment_024_1255_0020, g32p_row17_traceSegment_024_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_024 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1215 40 41, g32p_row17_traceSegment_024_1215_0040, g32p_row17_traceSegment_024_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_024_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_024 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 1134 81 81, g32p_row17_traceSegment_024_1134_0081, g32p_row17_traceSegment_024_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_024 972 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 972 162 162, g32p_row17_traceSegment_024_0972_0162, g32p_row17_traceSegment_024_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_024 648 648 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 648 324 324, g32p_row17_traceSegment_024_0648_0324, g32p_row17_traceSegment_024_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_024_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_024 0 1296 = [6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_024 0 648 648, g32p_row17_traceSegment_024_0000_0648, g32p_row17_traceSegment_024_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 24 = [6] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_024_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 11) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 11) (g32p_literalTraceValue 16 11)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_011]
  decide +kernel

theorem g32p_row17_tracePolynomial_013 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 13) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 13) (g32p_literalTraceValue 16 13)
      [1, -1, 1] [0, 0, 10368, 10368] = true := by
  rw [g32p_row17_traceCoefficients_013]
  decide +kernel

theorem g32p_row17_tracePolynomial_015 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 15) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 15) (g32p_literalTraceValue 16 15)
      [1, -1, 1] [1296, 1296, 1296] = true := by
  rw [g32p_row17_traceCoefficients_015]
  decide +kernel

theorem g32p_row17_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 18) (g32p_literalTraceValue 16 18)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_018]
  decide +kernel

theorem g32p_row17_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 19) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 19) (g32p_literalTraceValue 16 19)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_019]
  decide +kernel

theorem g32p_row17_tracePolynomial_021 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 21) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 21) (g32p_literalTraceValue 16 21)
      [1, -1, 1] [2592, 2592] = true := by
  rw [g32p_row17_traceCoefficients_021]
  decide +kernel

theorem g32p_row17_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 23) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 23) (g32p_literalTraceValue 16 23)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_023]
  decide +kernel

theorem g32p_row17_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 24) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 24) (g32p_literalTraceValue 16 24)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_024]
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

private def g32p_row17_traceSegment_025 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 25 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_025_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 0 10 10, g32p_row17_traceSegment_025_0000_0010, g32p_row17_traceSegment_025_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 20 10 10, g32p_row17_traceSegment_025_0020_0010, g32p_row17_traceSegment_025_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 0 20 20, g32p_row17_traceSegment_025_0000_0020, g32p_row17_traceSegment_025_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 40 10 10, g32p_row17_traceSegment_025_0040_0010, g32p_row17_traceSegment_025_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 60 10 11, g32p_row17_traceSegment_025_0060_0010, g32p_row17_traceSegment_025_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 40 20 21, g32p_row17_traceSegment_025_0040_0020, g32p_row17_traceSegment_025_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 0 40 41, g32p_row17_traceSegment_025_0000_0040, g32p_row17_traceSegment_025_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 81 10 10, g32p_row17_traceSegment_025_0081_0010, g32p_row17_traceSegment_025_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 101 10 10, g32p_row17_traceSegment_025_0101_0010, g32p_row17_traceSegment_025_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 81 20 20, g32p_row17_traceSegment_025_0081_0020, g32p_row17_traceSegment_025_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 121 10 10, g32p_row17_traceSegment_025_0121_0010, g32p_row17_traceSegment_025_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 141 10 11, g32p_row17_traceSegment_025_0141_0010, g32p_row17_traceSegment_025_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 121 20 21, g32p_row17_traceSegment_025_0121_0020, g32p_row17_traceSegment_025_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 81 40 41, g32p_row17_traceSegment_025_0081_0040, g32p_row17_traceSegment_025_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_025 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 0 81 81, g32p_row17_traceSegment_025_0000_0081, g32p_row17_traceSegment_025_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 162 10 10, g32p_row17_traceSegment_025_0162_0010, g32p_row17_traceSegment_025_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 182 10 10, g32p_row17_traceSegment_025_0182_0010, g32p_row17_traceSegment_025_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 162 20 20, g32p_row17_traceSegment_025_0162_0020, g32p_row17_traceSegment_025_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 202 10 10, g32p_row17_traceSegment_025_0202_0010, g32p_row17_traceSegment_025_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 222 10 11, g32p_row17_traceSegment_025_0222_0010, g32p_row17_traceSegment_025_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 202 20 21, g32p_row17_traceSegment_025_0202_0020, g32p_row17_traceSegment_025_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 162 40 41, g32p_row17_traceSegment_025_0162_0040, g32p_row17_traceSegment_025_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 243 10 10, g32p_row17_traceSegment_025_0243_0010, g32p_row17_traceSegment_025_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 263 10 10, g32p_row17_traceSegment_025_0263_0010, g32p_row17_traceSegment_025_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 243 20 20, g32p_row17_traceSegment_025_0243_0020, g32p_row17_traceSegment_025_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 283 10 10, g32p_row17_traceSegment_025_0283_0010, g32p_row17_traceSegment_025_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 303 10 11, g32p_row17_traceSegment_025_0303_0010, g32p_row17_traceSegment_025_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 283 20 21, g32p_row17_traceSegment_025_0283_0020, g32p_row17_traceSegment_025_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 243 40 41, g32p_row17_traceSegment_025_0243_0040, g32p_row17_traceSegment_025_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_025 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 162 81 81, g32p_row17_traceSegment_025_0162_0081, g32p_row17_traceSegment_025_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_025 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 0 162 162, g32p_row17_traceSegment_025_0000_0162, g32p_row17_traceSegment_025_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 324 10 10, g32p_row17_traceSegment_025_0324_0010, g32p_row17_traceSegment_025_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 344 10 10, g32p_row17_traceSegment_025_0344_0010, g32p_row17_traceSegment_025_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 324 20 20, g32p_row17_traceSegment_025_0324_0020, g32p_row17_traceSegment_025_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 364 10 10, g32p_row17_traceSegment_025_0364_0010, g32p_row17_traceSegment_025_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 384 10 11, g32p_row17_traceSegment_025_0384_0010, g32p_row17_traceSegment_025_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 364 20 21, g32p_row17_traceSegment_025_0364_0020, g32p_row17_traceSegment_025_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 324 40 41, g32p_row17_traceSegment_025_0324_0040, g32p_row17_traceSegment_025_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 405 10 10, g32p_row17_traceSegment_025_0405_0010, g32p_row17_traceSegment_025_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 425 10 10, g32p_row17_traceSegment_025_0425_0010, g32p_row17_traceSegment_025_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 405 20 20, g32p_row17_traceSegment_025_0405_0020, g32p_row17_traceSegment_025_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 445 10 10, g32p_row17_traceSegment_025_0445_0010, g32p_row17_traceSegment_025_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 465 10 11, g32p_row17_traceSegment_025_0465_0010, g32p_row17_traceSegment_025_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 445 20 21, g32p_row17_traceSegment_025_0445_0020, g32p_row17_traceSegment_025_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 405 40 41, g32p_row17_traceSegment_025_0405_0040, g32p_row17_traceSegment_025_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_025 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 324 81 81, g32p_row17_traceSegment_025_0324_0081, g32p_row17_traceSegment_025_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 486 10 10, g32p_row17_traceSegment_025_0486_0010, g32p_row17_traceSegment_025_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 506 10 10, g32p_row17_traceSegment_025_0506_0010, g32p_row17_traceSegment_025_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 486 20 20, g32p_row17_traceSegment_025_0486_0020, g32p_row17_traceSegment_025_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 526 10 10, g32p_row17_traceSegment_025_0526_0010, g32p_row17_traceSegment_025_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 546 10 11, g32p_row17_traceSegment_025_0546_0010, g32p_row17_traceSegment_025_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 526 20 21, g32p_row17_traceSegment_025_0526_0020, g32p_row17_traceSegment_025_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 486 40 41, g32p_row17_traceSegment_025_0486_0040, g32p_row17_traceSegment_025_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 577 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 567 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 567 10 10, g32p_row17_traceSegment_025_0567_0010, g32p_row17_traceSegment_025_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 587 10 10, g32p_row17_traceSegment_025_0587_0010, g32p_row17_traceSegment_025_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 567 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 567 20 20, g32p_row17_traceSegment_025_0567_0020, g32p_row17_traceSegment_025_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 607 10 10, g32p_row17_traceSegment_025_0607_0010, g32p_row17_traceSegment_025_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 627 10 11, g32p_row17_traceSegment_025_0627_0010, g32p_row17_traceSegment_025_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 607 20 21, g32p_row17_traceSegment_025_0607_0020, g32p_row17_traceSegment_025_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 567 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 567 40 41, g32p_row17_traceSegment_025_0567_0040, g32p_row17_traceSegment_025_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_025 486 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 486 81 81, g32p_row17_traceSegment_025_0486_0081, g32p_row17_traceSegment_025_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_025 324 324 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 324 162 162, g32p_row17_traceSegment_025_0324_0162, g32p_row17_traceSegment_025_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_025 0 648 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 0 324 324, g32p_row17_traceSegment_025_0000_0324, g32p_row17_traceSegment_025_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 658 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 648 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 648 10 10, g32p_row17_traceSegment_025_0648_0010, g32p_row17_traceSegment_025_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 668 10 10, g32p_row17_traceSegment_025_0668_0010, g32p_row17_traceSegment_025_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 648 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 648 20 20, g32p_row17_traceSegment_025_0648_0020, g32p_row17_traceSegment_025_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 688 10 10, g32p_row17_traceSegment_025_0688_0010, g32p_row17_traceSegment_025_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 708 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 708 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 708 10 11, g32p_row17_traceSegment_025_0708_0010, g32p_row17_traceSegment_025_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 688 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 688 20 21, g32p_row17_traceSegment_025_0688_0020, g32p_row17_traceSegment_025_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 648 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 648 40 41, g32p_row17_traceSegment_025_0648_0040, g32p_row17_traceSegment_025_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 729 10 10, g32p_row17_traceSegment_025_0729_0010, g32p_row17_traceSegment_025_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 749 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 749 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 749 10 10, g32p_row17_traceSegment_025_0749_0010, g32p_row17_traceSegment_025_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 729 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 729 20 20, g32p_row17_traceSegment_025_0729_0020, g32p_row17_traceSegment_025_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 769 10 10, g32p_row17_traceSegment_025_0769_0010, g32p_row17_traceSegment_025_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 789 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 789 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 789 10 11, g32p_row17_traceSegment_025_0789_0010, g32p_row17_traceSegment_025_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 769 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 769 20 21, g32p_row17_traceSegment_025_0769_0020, g32p_row17_traceSegment_025_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 729 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 729 40 41, g32p_row17_traceSegment_025_0729_0040, g32p_row17_traceSegment_025_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_025 648 162 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 648 81 81, g32p_row17_traceSegment_025_0648_0081, g32p_row17_traceSegment_025_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 810 10 10, g32p_row17_traceSegment_025_0810_0010, g32p_row17_traceSegment_025_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 830 10 10, g32p_row17_traceSegment_025_0830_0010, g32p_row17_traceSegment_025_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 810 20 20, g32p_row17_traceSegment_025_0810_0020, g32p_row17_traceSegment_025_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 850 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 850 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 850 10 10, g32p_row17_traceSegment_025_0850_0010, g32p_row17_traceSegment_025_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 870 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 870 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 870 10 11, g32p_row17_traceSegment_025_0870_0010, g32p_row17_traceSegment_025_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 850 41 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 850 20 21, g32p_row17_traceSegment_025_0850_0020, g32p_row17_traceSegment_025_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 810 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 810 40 41, g32p_row17_traceSegment_025_0810_0040, g32p_row17_traceSegment_025_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 891 10 10, g32p_row17_traceSegment_025_0891_0010, g32p_row17_traceSegment_025_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 911 10 10, g32p_row17_traceSegment_025_0911_0010, g32p_row17_traceSegment_025_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 891 20 20, g32p_row17_traceSegment_025_0891_0020, g32p_row17_traceSegment_025_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 931 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 931 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 931 10 10, g32p_row17_traceSegment_025_0931_0010, g32p_row17_traceSegment_025_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 951 10 11, g32p_row17_traceSegment_025_0951_0010, g32p_row17_traceSegment_025_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 931 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 931 20 21, g32p_row17_traceSegment_025_0931_0020, g32p_row17_traceSegment_025_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 891 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 891 40 41, g32p_row17_traceSegment_025_0891_0040, g32p_row17_traceSegment_025_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_025 810 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 810 81 81, g32p_row17_traceSegment_025_0810_0081, g32p_row17_traceSegment_025_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_025 648 324 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 648 162 162, g32p_row17_traceSegment_025_0648_0162, g32p_row17_traceSegment_025_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 972 10 10, g32p_row17_traceSegment_025_0972_0010, g32p_row17_traceSegment_025_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 992 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 992 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 992 10 10, g32p_row17_traceSegment_025_0992_0010, g32p_row17_traceSegment_025_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 972 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 972 20 20, g32p_row17_traceSegment_025_0972_0020, g32p_row17_traceSegment_025_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1012 10 10, g32p_row17_traceSegment_025_1012_0010, g32p_row17_traceSegment_025_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1032 10 11, g32p_row17_traceSegment_025_1032_0010, g32p_row17_traceSegment_025_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1012 20 21, g32p_row17_traceSegment_025_1012_0020, g32p_row17_traceSegment_025_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 972 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 972 40 41, g32p_row17_traceSegment_025_0972_0040, g32p_row17_traceSegment_025_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1053 10 10, g32p_row17_traceSegment_025_1053_0010, g32p_row17_traceSegment_025_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1073 10 10, g32p_row17_traceSegment_025_1073_0010, g32p_row17_traceSegment_025_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1053 20 20, g32p_row17_traceSegment_025_1053_0020, g32p_row17_traceSegment_025_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1093 10 10, g32p_row17_traceSegment_025_1093_0010, g32p_row17_traceSegment_025_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1113 10 11, g32p_row17_traceSegment_025_1113_0010, g32p_row17_traceSegment_025_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1093 20 21, g32p_row17_traceSegment_025_1093_0020, g32p_row17_traceSegment_025_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1053 40 41, g32p_row17_traceSegment_025_1053_0040, g32p_row17_traceSegment_025_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_025 972 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 972 81 81, g32p_row17_traceSegment_025_0972_0081, g32p_row17_traceSegment_025_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1134 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 1134 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1134 10 10, g32p_row17_traceSegment_025_1134_0010, g32p_row17_traceSegment_025_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1154 10 10, g32p_row17_traceSegment_025_1154_0010, g32p_row17_traceSegment_025_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 1134 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1134 20 20, g32p_row17_traceSegment_025_1134_0020, g32p_row17_traceSegment_025_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1184 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 1174 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1174 10 10, g32p_row17_traceSegment_025_1174_0010, g32p_row17_traceSegment_025_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1194 10 11, g32p_row17_traceSegment_025_1194_0010, g32p_row17_traceSegment_025_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 1174 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1174 20 21, g32p_row17_traceSegment_025_1174_0020, g32p_row17_traceSegment_025_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 1134 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1134 40 41, g32p_row17_traceSegment_025_1134_0040, g32p_row17_traceSegment_025_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1215 10 10, g32p_row17_traceSegment_025_1215_0010, g32p_row17_traceSegment_025_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1245 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 1235 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1235 10 10, g32p_row17_traceSegment_025_1235_0010, g32p_row17_traceSegment_025_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_025 1215 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1215 20 20, g32p_row17_traceSegment_025_1215_0020, g32p_row17_traceSegment_025_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_025 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1255 10 10, g32p_row17_traceSegment_025_1255_0010, g32p_row17_traceSegment_025_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_025 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_025 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_025_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_025 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1275 10 11, g32p_row17_traceSegment_025_1275_0010, g32p_row17_traceSegment_025_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_025 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1255 20 21, g32p_row17_traceSegment_025_1255_0020, g32p_row17_traceSegment_025_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_025 1215 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1215 40 41, g32p_row17_traceSegment_025_1215_0040, g32p_row17_traceSegment_025_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_025_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_025 1134 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 1134 81 81, g32p_row17_traceSegment_025_1134_0081, g32p_row17_traceSegment_025_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_025 972 324 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 972 162 162, g32p_row17_traceSegment_025_0972_0162, g32p_row17_traceSegment_025_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_025 648 648 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 648 324 324, g32p_row17_traceSegment_025_0648_0324, g32p_row17_traceSegment_025_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_025_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_025 0 1296 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_025 0 648 648, g32p_row17_traceSegment_025_0000_0648, g32p_row17_traceSegment_025_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_025 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 25 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_025_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_028 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 28 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_028_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 0 10 10, g32p_row17_traceSegment_028_0000_0010, g32p_row17_traceSegment_028_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 20 10 10, g32p_row17_traceSegment_028_0020_0010, g32p_row17_traceSegment_028_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 0 20 20, g32p_row17_traceSegment_028_0000_0020, g32p_row17_traceSegment_028_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 40 10 10, g32p_row17_traceSegment_028_0040_0010, g32p_row17_traceSegment_028_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 60 10 11, g32p_row17_traceSegment_028_0060_0010, g32p_row17_traceSegment_028_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 40 20 21, g32p_row17_traceSegment_028_0040_0020, g32p_row17_traceSegment_028_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 0 40 41, g32p_row17_traceSegment_028_0000_0040, g32p_row17_traceSegment_028_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 81 10 10, g32p_row17_traceSegment_028_0081_0010, g32p_row17_traceSegment_028_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 101 10 10, g32p_row17_traceSegment_028_0101_0010, g32p_row17_traceSegment_028_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 81 20 20, g32p_row17_traceSegment_028_0081_0020, g32p_row17_traceSegment_028_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 121 10 10, g32p_row17_traceSegment_028_0121_0010, g32p_row17_traceSegment_028_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 141 10 11, g32p_row17_traceSegment_028_0141_0010, g32p_row17_traceSegment_028_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 121 20 21, g32p_row17_traceSegment_028_0121_0020, g32p_row17_traceSegment_028_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 81 40 41, g32p_row17_traceSegment_028_0081_0040, g32p_row17_traceSegment_028_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_028 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 0 81 81, g32p_row17_traceSegment_028_0000_0081, g32p_row17_traceSegment_028_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 162 10 10, g32p_row17_traceSegment_028_0162_0010, g32p_row17_traceSegment_028_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 182 10 10, g32p_row17_traceSegment_028_0182_0010, g32p_row17_traceSegment_028_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 162 20 20, g32p_row17_traceSegment_028_0162_0020, g32p_row17_traceSegment_028_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 202 10 10, g32p_row17_traceSegment_028_0202_0010, g32p_row17_traceSegment_028_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 222 10 11, g32p_row17_traceSegment_028_0222_0010, g32p_row17_traceSegment_028_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 202 20 21, g32p_row17_traceSegment_028_0202_0020, g32p_row17_traceSegment_028_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 162 40 41, g32p_row17_traceSegment_028_0162_0040, g32p_row17_traceSegment_028_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 243 10 10, g32p_row17_traceSegment_028_0243_0010, g32p_row17_traceSegment_028_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 263 10 10, g32p_row17_traceSegment_028_0263_0010, g32p_row17_traceSegment_028_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 243 20 20, g32p_row17_traceSegment_028_0243_0020, g32p_row17_traceSegment_028_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 283 10 10, g32p_row17_traceSegment_028_0283_0010, g32p_row17_traceSegment_028_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 303 10 11, g32p_row17_traceSegment_028_0303_0010, g32p_row17_traceSegment_028_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 283 20 21, g32p_row17_traceSegment_028_0283_0020, g32p_row17_traceSegment_028_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 243 40 41, g32p_row17_traceSegment_028_0243_0040, g32p_row17_traceSegment_028_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_028 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 162 81 81, g32p_row17_traceSegment_028_0162_0081, g32p_row17_traceSegment_028_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_028 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 0 162 162, g32p_row17_traceSegment_028_0000_0162, g32p_row17_traceSegment_028_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 324 10 10, g32p_row17_traceSegment_028_0324_0010, g32p_row17_traceSegment_028_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 344 10 10, g32p_row17_traceSegment_028_0344_0010, g32p_row17_traceSegment_028_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 324 20 20, g32p_row17_traceSegment_028_0324_0020, g32p_row17_traceSegment_028_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 364 10 10, g32p_row17_traceSegment_028_0364_0010, g32p_row17_traceSegment_028_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 384 10 11, g32p_row17_traceSegment_028_0384_0010, g32p_row17_traceSegment_028_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 364 20 21, g32p_row17_traceSegment_028_0364_0020, g32p_row17_traceSegment_028_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 324 40 41, g32p_row17_traceSegment_028_0324_0040, g32p_row17_traceSegment_028_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 405 10 10, g32p_row17_traceSegment_028_0405_0010, g32p_row17_traceSegment_028_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 425 10 10, g32p_row17_traceSegment_028_0425_0010, g32p_row17_traceSegment_028_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 405 20 20, g32p_row17_traceSegment_028_0405_0020, g32p_row17_traceSegment_028_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 445 10 10, g32p_row17_traceSegment_028_0445_0010, g32p_row17_traceSegment_028_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 465 10 11, g32p_row17_traceSegment_028_0465_0010, g32p_row17_traceSegment_028_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 445 20 21, g32p_row17_traceSegment_028_0445_0020, g32p_row17_traceSegment_028_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 405 40 41, g32p_row17_traceSegment_028_0405_0040, g32p_row17_traceSegment_028_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_028 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 324 81 81, g32p_row17_traceSegment_028_0324_0081, g32p_row17_traceSegment_028_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 486 10 10, g32p_row17_traceSegment_028_0486_0010, g32p_row17_traceSegment_028_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 506 10 10, g32p_row17_traceSegment_028_0506_0010, g32p_row17_traceSegment_028_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 486 20 20, g32p_row17_traceSegment_028_0486_0020, g32p_row17_traceSegment_028_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 526 10 10, g32p_row17_traceSegment_028_0526_0010, g32p_row17_traceSegment_028_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 546 10 11, g32p_row17_traceSegment_028_0546_0010, g32p_row17_traceSegment_028_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 526 20 21, g32p_row17_traceSegment_028_0526_0020, g32p_row17_traceSegment_028_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 486 40 41, g32p_row17_traceSegment_028_0486_0040, g32p_row17_traceSegment_028_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 567 10 10, g32p_row17_traceSegment_028_0567_0010, g32p_row17_traceSegment_028_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 587 10 10, g32p_row17_traceSegment_028_0587_0010, g32p_row17_traceSegment_028_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 567 20 20, g32p_row17_traceSegment_028_0567_0020, g32p_row17_traceSegment_028_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 607 10 10, g32p_row17_traceSegment_028_0607_0010, g32p_row17_traceSegment_028_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 627 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 627 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 627 10 11, g32p_row17_traceSegment_028_0627_0010, g32p_row17_traceSegment_028_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 607 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 607 20 21, g32p_row17_traceSegment_028_0607_0020, g32p_row17_traceSegment_028_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 567 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 567 40 41, g32p_row17_traceSegment_028_0567_0040, g32p_row17_traceSegment_028_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_028 486 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 486 81 81, g32p_row17_traceSegment_028_0486_0081, g32p_row17_traceSegment_028_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_028 324 324 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 324 162 162, g32p_row17_traceSegment_028_0324_0162, g32p_row17_traceSegment_028_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_028 0 648 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 0 324 324, g32p_row17_traceSegment_028_0000_0324, g32p_row17_traceSegment_028_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 648 10 10, g32p_row17_traceSegment_028_0648_0010, g32p_row17_traceSegment_028_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 668 10 10, g32p_row17_traceSegment_028_0668_0010, g32p_row17_traceSegment_028_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 648 20 20, g32p_row17_traceSegment_028_0648_0020, g32p_row17_traceSegment_028_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 688 10 10, g32p_row17_traceSegment_028_0688_0010, g32p_row17_traceSegment_028_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 708 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 708 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 708 10 11, g32p_row17_traceSegment_028_0708_0010, g32p_row17_traceSegment_028_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 688 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 688 20 21, g32p_row17_traceSegment_028_0688_0020, g32p_row17_traceSegment_028_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 648 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 648 40 41, g32p_row17_traceSegment_028_0648_0040, g32p_row17_traceSegment_028_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 729 10 10, g32p_row17_traceSegment_028_0729_0010, g32p_row17_traceSegment_028_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 749 10 10, g32p_row17_traceSegment_028_0749_0010, g32p_row17_traceSegment_028_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 729 20 20, g32p_row17_traceSegment_028_0729_0020, g32p_row17_traceSegment_028_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 769 10 10, g32p_row17_traceSegment_028_0769_0010, g32p_row17_traceSegment_028_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 799 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 789 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 789 10 11, g32p_row17_traceSegment_028_0789_0010, g32p_row17_traceSegment_028_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 769 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 769 20 21, g32p_row17_traceSegment_028_0769_0020, g32p_row17_traceSegment_028_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 729 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 729 40 41, g32p_row17_traceSegment_028_0729_0040, g32p_row17_traceSegment_028_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_028 648 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 648 81 81, g32p_row17_traceSegment_028_0648_0081, g32p_row17_traceSegment_028_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 810 10 10, g32p_row17_traceSegment_028_0810_0010, g32p_row17_traceSegment_028_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 830 10 10, g32p_row17_traceSegment_028_0830_0010, g32p_row17_traceSegment_028_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 810 20 20, g32p_row17_traceSegment_028_0810_0020, g32p_row17_traceSegment_028_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 850 10 10, g32p_row17_traceSegment_028_0850_0010, g32p_row17_traceSegment_028_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 870 10 11, g32p_row17_traceSegment_028_0870_0010, g32p_row17_traceSegment_028_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 850 20 21, g32p_row17_traceSegment_028_0850_0020, g32p_row17_traceSegment_028_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 810 40 41, g32p_row17_traceSegment_028_0810_0040, g32p_row17_traceSegment_028_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 891 10 10, g32p_row17_traceSegment_028_0891_0010, g32p_row17_traceSegment_028_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 911 10 10, g32p_row17_traceSegment_028_0911_0010, g32p_row17_traceSegment_028_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 891 20 20, g32p_row17_traceSegment_028_0891_0020, g32p_row17_traceSegment_028_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 931 10 10, g32p_row17_traceSegment_028_0931_0010, g32p_row17_traceSegment_028_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 951 10 11, g32p_row17_traceSegment_028_0951_0010, g32p_row17_traceSegment_028_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 931 20 21, g32p_row17_traceSegment_028_0931_0020, g32p_row17_traceSegment_028_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 891 40 41, g32p_row17_traceSegment_028_0891_0040, g32p_row17_traceSegment_028_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_028 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 810 81 81, g32p_row17_traceSegment_028_0810_0081, g32p_row17_traceSegment_028_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_028 648 324 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 648 162 162, g32p_row17_traceSegment_028_0648_0162, g32p_row17_traceSegment_028_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 972 10 10, g32p_row17_traceSegment_028_0972_0010, g32p_row17_traceSegment_028_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 992 10 10, g32p_row17_traceSegment_028_0992_0010, g32p_row17_traceSegment_028_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 972 20 20, g32p_row17_traceSegment_028_0972_0020, g32p_row17_traceSegment_028_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1012 10 10, g32p_row17_traceSegment_028_1012_0010, g32p_row17_traceSegment_028_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1032 10 11, g32p_row17_traceSegment_028_1032_0010, g32p_row17_traceSegment_028_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1012 20 21, g32p_row17_traceSegment_028_1012_0020, g32p_row17_traceSegment_028_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 972 40 41, g32p_row17_traceSegment_028_0972_0040, g32p_row17_traceSegment_028_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1053 10 10, g32p_row17_traceSegment_028_1053_0010, g32p_row17_traceSegment_028_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1073 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 1073 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1073 10 10, g32p_row17_traceSegment_028_1073_0010, g32p_row17_traceSegment_028_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 1053 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1053 20 20, g32p_row17_traceSegment_028_1053_0020, g32p_row17_traceSegment_028_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1093 10 10, g32p_row17_traceSegment_028_1093_0010, g32p_row17_traceSegment_028_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1113 10 11, g32p_row17_traceSegment_028_1113_0010, g32p_row17_traceSegment_028_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1093 20 21, g32p_row17_traceSegment_028_1093_0020, g32p_row17_traceSegment_028_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 1053 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1053 40 41, g32p_row17_traceSegment_028_1053_0040, g32p_row17_traceSegment_028_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_028 972 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 972 81 81, g32p_row17_traceSegment_028_0972_0081, g32p_row17_traceSegment_028_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1134 10 10, g32p_row17_traceSegment_028_1134_0010, g32p_row17_traceSegment_028_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1154 10 10, g32p_row17_traceSegment_028_1154_0010, g32p_row17_traceSegment_028_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1134 20 20, g32p_row17_traceSegment_028_1134_0020, g32p_row17_traceSegment_028_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1174 10 10, g32p_row17_traceSegment_028_1174_0010, g32p_row17_traceSegment_028_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1194 10 11, g32p_row17_traceSegment_028_1194_0010, g32p_row17_traceSegment_028_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1174 20 21, g32p_row17_traceSegment_028_1174_0020, g32p_row17_traceSegment_028_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1134 40 41, g32p_row17_traceSegment_028_1134_0040, g32p_row17_traceSegment_028_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1215 10 10, g32p_row17_traceSegment_028_1215_0010, g32p_row17_traceSegment_028_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1235 10 10, g32p_row17_traceSegment_028_1235_0010, g32p_row17_traceSegment_028_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_028 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1215 20 20, g32p_row17_traceSegment_028_1215_0020, g32p_row17_traceSegment_028_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_028 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1255 10 10, g32p_row17_traceSegment_028_1255_0010, g32p_row17_traceSegment_028_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_028 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_028 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_028_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_028 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1275 10 11, g32p_row17_traceSegment_028_1275_0010, g32p_row17_traceSegment_028_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_028 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1255 20 21, g32p_row17_traceSegment_028_1255_0020, g32p_row17_traceSegment_028_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_028 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1215 40 41, g32p_row17_traceSegment_028_1215_0040, g32p_row17_traceSegment_028_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_028_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_028 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 1134 81 81, g32p_row17_traceSegment_028_1134_0081, g32p_row17_traceSegment_028_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_028 972 324 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 972 162 162, g32p_row17_traceSegment_028_0972_0162, g32p_row17_traceSegment_028_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_028 648 648 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 648 324 324, g32p_row17_traceSegment_028_0648_0324, g32p_row17_traceSegment_028_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_028_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_028 0 1296 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_028 0 648 648, g32p_row17_traceSegment_028_0000_0648, g32p_row17_traceSegment_028_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_028 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 28 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_028_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_029 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 29 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_029_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 0 10 10, g32p_row17_traceSegment_029_0000_0010, g32p_row17_traceSegment_029_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 20 10 10, g32p_row17_traceSegment_029_0020_0010, g32p_row17_traceSegment_029_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 0 20 20, g32p_row17_traceSegment_029_0000_0020, g32p_row17_traceSegment_029_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 40 10 10, g32p_row17_traceSegment_029_0040_0010, g32p_row17_traceSegment_029_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 60 10 11, g32p_row17_traceSegment_029_0060_0010, g32p_row17_traceSegment_029_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 40 20 21, g32p_row17_traceSegment_029_0040_0020, g32p_row17_traceSegment_029_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 0 40 41, g32p_row17_traceSegment_029_0000_0040, g32p_row17_traceSegment_029_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 81 10 10, g32p_row17_traceSegment_029_0081_0010, g32p_row17_traceSegment_029_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 101 10 10, g32p_row17_traceSegment_029_0101_0010, g32p_row17_traceSegment_029_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 81 20 20, g32p_row17_traceSegment_029_0081_0020, g32p_row17_traceSegment_029_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 121 10 10, g32p_row17_traceSegment_029_0121_0010, g32p_row17_traceSegment_029_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 141 10 11, g32p_row17_traceSegment_029_0141_0010, g32p_row17_traceSegment_029_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 121 20 21, g32p_row17_traceSegment_029_0121_0020, g32p_row17_traceSegment_029_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 81 40 41, g32p_row17_traceSegment_029_0081_0040, g32p_row17_traceSegment_029_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_029 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 0 81 81, g32p_row17_traceSegment_029_0000_0081, g32p_row17_traceSegment_029_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 162 10 10, g32p_row17_traceSegment_029_0162_0010, g32p_row17_traceSegment_029_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 182 10 10, g32p_row17_traceSegment_029_0182_0010, g32p_row17_traceSegment_029_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 162 20 20, g32p_row17_traceSegment_029_0162_0020, g32p_row17_traceSegment_029_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 202 10 10, g32p_row17_traceSegment_029_0202_0010, g32p_row17_traceSegment_029_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 222 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 222 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 222 10 11, g32p_row17_traceSegment_029_0222_0010, g32p_row17_traceSegment_029_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 202 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 202 20 21, g32p_row17_traceSegment_029_0202_0020, g32p_row17_traceSegment_029_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 162 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 162 40 41, g32p_row17_traceSegment_029_0162_0040, g32p_row17_traceSegment_029_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 243 10 10, g32p_row17_traceSegment_029_0243_0010, g32p_row17_traceSegment_029_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 263 10 10, g32p_row17_traceSegment_029_0263_0010, g32p_row17_traceSegment_029_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 243 20 20, g32p_row17_traceSegment_029_0243_0020, g32p_row17_traceSegment_029_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 293 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 283 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 283 10 10, g32p_row17_traceSegment_029_0283_0010, g32p_row17_traceSegment_029_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 303 10 11, g32p_row17_traceSegment_029_0303_0010, g32p_row17_traceSegment_029_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 283 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 283 20 21, g32p_row17_traceSegment_029_0283_0020, g32p_row17_traceSegment_029_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 243 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 243 40 41, g32p_row17_traceSegment_029_0243_0040, g32p_row17_traceSegment_029_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_029 162 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 162 81 81, g32p_row17_traceSegment_029_0162_0081, g32p_row17_traceSegment_029_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_029 0 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 0 162 162, g32p_row17_traceSegment_029_0000_0162, g32p_row17_traceSegment_029_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 324 10 10, g32p_row17_traceSegment_029_0324_0010, g32p_row17_traceSegment_029_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 344 10 10, g32p_row17_traceSegment_029_0344_0010, g32p_row17_traceSegment_029_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 324 20 20, g32p_row17_traceSegment_029_0324_0020, g32p_row17_traceSegment_029_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 374 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 364 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 364 10 10, g32p_row17_traceSegment_029_0364_0010, g32p_row17_traceSegment_029_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 384 10 11, g32p_row17_traceSegment_029_0384_0010, g32p_row17_traceSegment_029_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 364 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 364 20 21, g32p_row17_traceSegment_029_0364_0020, g32p_row17_traceSegment_029_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 324 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 324 40 41, g32p_row17_traceSegment_029_0324_0040, g32p_row17_traceSegment_029_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 415 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 405 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 405 10 10, g32p_row17_traceSegment_029_0405_0010, g32p_row17_traceSegment_029_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 425 10 10, g32p_row17_traceSegment_029_0425_0010, g32p_row17_traceSegment_029_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 405 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 405 20 20, g32p_row17_traceSegment_029_0405_0020, g32p_row17_traceSegment_029_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 455 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 445 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 445 10 10, g32p_row17_traceSegment_029_0445_0010, g32p_row17_traceSegment_029_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 465 10 11, g32p_row17_traceSegment_029_0465_0010, g32p_row17_traceSegment_029_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 445 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 445 20 21, g32p_row17_traceSegment_029_0445_0020, g32p_row17_traceSegment_029_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 405 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 405 40 41, g32p_row17_traceSegment_029_0405_0040, g32p_row17_traceSegment_029_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_029 324 162 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 324 81 81, g32p_row17_traceSegment_029_0324_0081, g32p_row17_traceSegment_029_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 486 10 10, g32p_row17_traceSegment_029_0486_0010, g32p_row17_traceSegment_029_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 506 10 10, g32p_row17_traceSegment_029_0506_0010, g32p_row17_traceSegment_029_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 486 20 20, g32p_row17_traceSegment_029_0486_0020, g32p_row17_traceSegment_029_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 526 10 10, g32p_row17_traceSegment_029_0526_0010, g32p_row17_traceSegment_029_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 546 10 11, g32p_row17_traceSegment_029_0546_0010, g32p_row17_traceSegment_029_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 526 20 21, g32p_row17_traceSegment_029_0526_0020, g32p_row17_traceSegment_029_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 486 40 41, g32p_row17_traceSegment_029_0486_0040, g32p_row17_traceSegment_029_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 567 10 10, g32p_row17_traceSegment_029_0567_0010, g32p_row17_traceSegment_029_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 587 10 10, g32p_row17_traceSegment_029_0587_0010, g32p_row17_traceSegment_029_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 567 20 20, g32p_row17_traceSegment_029_0567_0020, g32p_row17_traceSegment_029_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 607 10 10, g32p_row17_traceSegment_029_0607_0010, g32p_row17_traceSegment_029_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 627 10 11, g32p_row17_traceSegment_029_0627_0010, g32p_row17_traceSegment_029_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 607 20 21, g32p_row17_traceSegment_029_0607_0020, g32p_row17_traceSegment_029_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 567 40 41, g32p_row17_traceSegment_029_0567_0040, g32p_row17_traceSegment_029_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_029 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 486 81 81, g32p_row17_traceSegment_029_0486_0081, g32p_row17_traceSegment_029_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_029 324 324 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 324 162 162, g32p_row17_traceSegment_029_0324_0162, g32p_row17_traceSegment_029_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_029 0 648 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 0 324 324, g32p_row17_traceSegment_029_0000_0324, g32p_row17_traceSegment_029_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 648 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 648 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 648 10 10, g32p_row17_traceSegment_029_0648_0010, g32p_row17_traceSegment_029_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 668 10 10, g32p_row17_traceSegment_029_0668_0010, g32p_row17_traceSegment_029_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 648 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 648 20 20, g32p_row17_traceSegment_029_0648_0020, g32p_row17_traceSegment_029_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 688 10 10, g32p_row17_traceSegment_029_0688_0010, g32p_row17_traceSegment_029_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 708 10 11, g32p_row17_traceSegment_029_0708_0010, g32p_row17_traceSegment_029_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 688 20 21, g32p_row17_traceSegment_029_0688_0020, g32p_row17_traceSegment_029_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 648 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 648 40 41, g32p_row17_traceSegment_029_0648_0040, g32p_row17_traceSegment_029_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 729 10 10, g32p_row17_traceSegment_029_0729_0010, g32p_row17_traceSegment_029_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 749 10 10, g32p_row17_traceSegment_029_0749_0010, g32p_row17_traceSegment_029_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 729 20 20, g32p_row17_traceSegment_029_0729_0020, g32p_row17_traceSegment_029_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 769 10 10, g32p_row17_traceSegment_029_0769_0010, g32p_row17_traceSegment_029_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 789 10 11, g32p_row17_traceSegment_029_0789_0010, g32p_row17_traceSegment_029_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 769 20 21, g32p_row17_traceSegment_029_0769_0020, g32p_row17_traceSegment_029_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 729 40 41, g32p_row17_traceSegment_029_0729_0040, g32p_row17_traceSegment_029_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_029 648 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 648 81 81, g32p_row17_traceSegment_029_0648_0081, g32p_row17_traceSegment_029_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 810 10 10, g32p_row17_traceSegment_029_0810_0010, g32p_row17_traceSegment_029_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 840 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 830 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 830 10 10, g32p_row17_traceSegment_029_0830_0010, g32p_row17_traceSegment_029_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 810 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 810 20 20, g32p_row17_traceSegment_029_0810_0020, g32p_row17_traceSegment_029_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 850 10 10, g32p_row17_traceSegment_029_0850_0010, g32p_row17_traceSegment_029_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 870 10 11, g32p_row17_traceSegment_029_0870_0010, g32p_row17_traceSegment_029_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 850 20 21, g32p_row17_traceSegment_029_0850_0020, g32p_row17_traceSegment_029_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 810 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 810 40 41, g32p_row17_traceSegment_029_0810_0040, g32p_row17_traceSegment_029_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 891 10 10, g32p_row17_traceSegment_029_0891_0010, g32p_row17_traceSegment_029_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 911 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 911 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 911 10 10, g32p_row17_traceSegment_029_0911_0010, g32p_row17_traceSegment_029_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 891 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 891 20 20, g32p_row17_traceSegment_029_0891_0020, g32p_row17_traceSegment_029_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 931 10 10, g32p_row17_traceSegment_029_0931_0010, g32p_row17_traceSegment_029_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 951 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 951 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 951 10 11, g32p_row17_traceSegment_029_0951_0010, g32p_row17_traceSegment_029_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 931 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 931 20 21, g32p_row17_traceSegment_029_0931_0020, g32p_row17_traceSegment_029_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 891 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 891 40 41, g32p_row17_traceSegment_029_0891_0040, g32p_row17_traceSegment_029_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_029 810 162 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 810 81 81, g32p_row17_traceSegment_029_0810_0081, g32p_row17_traceSegment_029_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_029 648 324 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 648 162 162, g32p_row17_traceSegment_029_0648_0162, g32p_row17_traceSegment_029_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 972 10 10, g32p_row17_traceSegment_029_0972_0010, g32p_row17_traceSegment_029_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 992 10 10, g32p_row17_traceSegment_029_0992_0010, g32p_row17_traceSegment_029_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 972 20 20, g32p_row17_traceSegment_029_0972_0020, g32p_row17_traceSegment_029_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1012 10 10, g32p_row17_traceSegment_029_1012_0010, g32p_row17_traceSegment_029_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1032 10 11, g32p_row17_traceSegment_029_1032_0010, g32p_row17_traceSegment_029_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1012 20 21, g32p_row17_traceSegment_029_1012_0020, g32p_row17_traceSegment_029_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 972 40 41, g32p_row17_traceSegment_029_0972_0040, g32p_row17_traceSegment_029_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1063 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 1053 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1053 10 10, g32p_row17_traceSegment_029_1053_0010, g32p_row17_traceSegment_029_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1073 10 10, g32p_row17_traceSegment_029_1073_0010, g32p_row17_traceSegment_029_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 1053 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1053 20 20, g32p_row17_traceSegment_029_1053_0020, g32p_row17_traceSegment_029_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1093 10 10, g32p_row17_traceSegment_029_1093_0010, g32p_row17_traceSegment_029_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1113 10 11, g32p_row17_traceSegment_029_1113_0010, g32p_row17_traceSegment_029_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1093 20 21, g32p_row17_traceSegment_029_1093_0020, g32p_row17_traceSegment_029_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 1053 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1053 40 41, g32p_row17_traceSegment_029_1053_0040, g32p_row17_traceSegment_029_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_029 972 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 972 81 81, g32p_row17_traceSegment_029_0972_0081, g32p_row17_traceSegment_029_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1144 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 1134 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1134 10 10, g32p_row17_traceSegment_029_1134_0010, g32p_row17_traceSegment_029_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1154 10 10, g32p_row17_traceSegment_029_1154_0010, g32p_row17_traceSegment_029_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 1134 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1134 20 20, g32p_row17_traceSegment_029_1134_0020, g32p_row17_traceSegment_029_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1174 10 10, g32p_row17_traceSegment_029_1174_0010, g32p_row17_traceSegment_029_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1194 10 11, g32p_row17_traceSegment_029_1194_0010, g32p_row17_traceSegment_029_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1174 20 21, g32p_row17_traceSegment_029_1174_0020, g32p_row17_traceSegment_029_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 1134 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1134 40 41, g32p_row17_traceSegment_029_1134_0040, g32p_row17_traceSegment_029_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1215 10 10, g32p_row17_traceSegment_029_1215_0010, g32p_row17_traceSegment_029_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1245 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 1235 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1235 10 10, g32p_row17_traceSegment_029_1235_0010, g32p_row17_traceSegment_029_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_029 1215 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1215 20 20, g32p_row17_traceSegment_029_1215_0020, g32p_row17_traceSegment_029_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_029 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1255 10 10, g32p_row17_traceSegment_029_1255_0010, g32p_row17_traceSegment_029_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_029 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_029 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_029_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_029 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1275 10 11, g32p_row17_traceSegment_029_1275_0010, g32p_row17_traceSegment_029_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_029 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1255 20 21, g32p_row17_traceSegment_029_1255_0020, g32p_row17_traceSegment_029_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_029 1215 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1215 40 41, g32p_row17_traceSegment_029_1215_0040, g32p_row17_traceSegment_029_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_029_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_029 1134 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 1134 81 81, g32p_row17_traceSegment_029_1134_0081, g32p_row17_traceSegment_029_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_029 972 324 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 972 162 162, g32p_row17_traceSegment_029_0972_0162, g32p_row17_traceSegment_029_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_029 648 648 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 648 324 324, g32p_row17_traceSegment_029_0648_0324, g32p_row17_traceSegment_029_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_029_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_029 0 1296 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_029 0 648 648, g32p_row17_traceSegment_029_0000_0648, g32p_row17_traceSegment_029_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_029 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 29 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_029_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_030 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 30 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_030_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 0 10 10, g32p_row17_traceSegment_030_0000_0010, g32p_row17_traceSegment_030_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 20 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 20 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 20 10 10, g32p_row17_traceSegment_030_0020_0010, g32p_row17_traceSegment_030_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 0 40 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 0 20 20, g32p_row17_traceSegment_030_0000_0020, g32p_row17_traceSegment_030_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 40 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 40 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 40 10 10, g32p_row17_traceSegment_030_0040_0010, g32p_row17_traceSegment_030_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 60 10 11, g32p_row17_traceSegment_030_0060_0010, g32p_row17_traceSegment_030_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 40 41 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 40 20 21, g32p_row17_traceSegment_030_0040_0020, g32p_row17_traceSegment_030_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 0 81 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 0 40 41, g32p_row17_traceSegment_030_0000_0040, g32p_row17_traceSegment_030_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 81 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 91 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 81 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 81 10 10, g32p_row17_traceSegment_030_0081_0010, g32p_row17_traceSegment_030_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 101 10 10, g32p_row17_traceSegment_030_0101_0010, g32p_row17_traceSegment_030_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 81 40 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 81 20 20, g32p_row17_traceSegment_030_0081_0020, g32p_row17_traceSegment_030_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 131 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 121 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 121 10 10, g32p_row17_traceSegment_030_0121_0010, g32p_row17_traceSegment_030_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 151 11 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 141 21 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 141 10 11, g32p_row17_traceSegment_030_0141_0010, g32p_row17_traceSegment_030_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 121 41 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 121 20 21, g32p_row17_traceSegment_030_0121_0020, g32p_row17_traceSegment_030_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 81 81 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 81 40 41, g32p_row17_traceSegment_030_0081_0040, g32p_row17_traceSegment_030_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_030 0 162 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 0 81 81, g32p_row17_traceSegment_030_0000_0081, g32p_row17_traceSegment_030_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 162 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 172 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 162 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 162 10 10, g32p_row17_traceSegment_030_0162_0010, g32p_row17_traceSegment_030_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 182 10 10, g32p_row17_traceSegment_030_0182_0010, g32p_row17_traceSegment_030_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 162 40 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 162 20 20, g32p_row17_traceSegment_030_0162_0020, g32p_row17_traceSegment_030_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 212 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 202 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 202 10 10, g32p_row17_traceSegment_030_0202_0010, g32p_row17_traceSegment_030_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 232 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 222 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 222 10 11, g32p_row17_traceSegment_030_0222_0010, g32p_row17_traceSegment_030_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 202 41 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 202 20 21, g32p_row17_traceSegment_030_0202_0020, g32p_row17_traceSegment_030_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 162 81 = [0, 4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 162 40 41, g32p_row17_traceSegment_030_0162_0040, g32p_row17_traceSegment_030_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 243 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 243 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 243 10 10, g32p_row17_traceSegment_030_0243_0010, g32p_row17_traceSegment_030_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 273 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 263 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 263 10 10, g32p_row17_traceSegment_030_0263_0010, g32p_row17_traceSegment_030_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 243 40 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 243 20 20, g32p_row17_traceSegment_030_0243_0020, g32p_row17_traceSegment_030_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 283 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 293 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 283 20 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 283 10 10, g32p_row17_traceSegment_030_0283_0010, g32p_row17_traceSegment_030_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 303 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 313 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 303 21 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 303 10 11, g32p_row17_traceSegment_030_0303_0010, g32p_row17_traceSegment_030_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 283 41 = [0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 283 20 21, g32p_row17_traceSegment_030_0283_0020, g32p_row17_traceSegment_030_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 243 81 = [0, 4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 243 40 41, g32p_row17_traceSegment_030_0243_0040, g32p_row17_traceSegment_030_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_030 162 162 = [0, 8, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 162 81 81, g32p_row17_traceSegment_030_0162_0081, g32p_row17_traceSegment_030_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_030 0 324 = [0, 17, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 0 162 162, g32p_row17_traceSegment_030_0000_0162, g32p_row17_traceSegment_030_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 324 10 = [0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 324 20 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 324 10 10, g32p_row17_traceSegment_030_0324_0010, g32p_row17_traceSegment_030_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 344 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 344 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 344 10 10, g32p_row17_traceSegment_030_0344_0010, g32p_row17_traceSegment_030_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 324 40 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 324 20 20, g32p_row17_traceSegment_030_0324_0020, g32p_row17_traceSegment_030_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 374 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 364 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 364 10 10, g32p_row17_traceSegment_030_0364_0010, g32p_row17_traceSegment_030_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 384 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 384 21 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 384 10 11, g32p_row17_traceSegment_030_0384_0010, g32p_row17_traceSegment_030_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 364 41 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 364 20 21, g32p_row17_traceSegment_030_0364_0020, g32p_row17_traceSegment_030_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 324 81 = [0, 5, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 324 40 41, g32p_row17_traceSegment_030_0324_0040, g32p_row17_traceSegment_030_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 405 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 415 10 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 405 20 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 405 10 10, g32p_row17_traceSegment_030_0405_0010, g32p_row17_traceSegment_030_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 425 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 435 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 425 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 425 10 10, g32p_row17_traceSegment_030_0425_0010, g32p_row17_traceSegment_030_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 405 40 = [0, 5, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 405 20 20, g32p_row17_traceSegment_030_0405_0020, g32p_row17_traceSegment_030_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 445 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 455 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 445 20 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 445 10 10, g32p_row17_traceSegment_030_0445_0010, g32p_row17_traceSegment_030_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 465 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 475 11 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 465 21 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 465 10 11, g32p_row17_traceSegment_030_0465_0010, g32p_row17_traceSegment_030_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 445 41 = [0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 445 20 21, g32p_row17_traceSegment_030_0445_0020, g32p_row17_traceSegment_030_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 405 81 = [0, 8, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 405 40 41, g32p_row17_traceSegment_030_0405_0040, g32p_row17_traceSegment_030_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_030 324 162 = [0, 13, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 324 81 81, g32p_row17_traceSegment_030_0324_0081, g32p_row17_traceSegment_030_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 496 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 486 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 486 10 10, g32p_row17_traceSegment_030_0486_0010, g32p_row17_traceSegment_030_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 506 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 516 10 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 506 20 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 506 10 10, g32p_row17_traceSegment_030_0506_0010, g32p_row17_traceSegment_030_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 486 40 = [0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 486 20 20, g32p_row17_traceSegment_030_0486_0020, g32p_row17_traceSegment_030_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 526 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 536 10 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 526 20 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 526 10 10, g32p_row17_traceSegment_030_0526_0010, g32p_row17_traceSegment_030_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 546 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 556 11 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 546 21 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 546 10 11, g32p_row17_traceSegment_030_0546_0010, g32p_row17_traceSegment_030_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 526 41 = [0, 6, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 526 20 21, g32p_row17_traceSegment_030_0526_0020, g32p_row17_traceSegment_030_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 486 81 = [0, 7, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 486 40 41, g32p_row17_traceSegment_030_0486_0040, g32p_row17_traceSegment_030_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 567 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 567 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 567 10 10, g32p_row17_traceSegment_030_0567_0010, g32p_row17_traceSegment_030_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 597 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 587 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 587 10 10, g32p_row17_traceSegment_030_0587_0010, g32p_row17_traceSegment_030_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 567 40 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 567 20 20, g32p_row17_traceSegment_030_0567_0020, g32p_row17_traceSegment_030_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 607 10 10, g32p_row17_traceSegment_030_0607_0010, g32p_row17_traceSegment_030_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 637 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 627 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 627 10 11, g32p_row17_traceSegment_030_0627_0010, g32p_row17_traceSegment_030_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 607 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 607 20 21, g32p_row17_traceSegment_030_0607_0020, g32p_row17_traceSegment_030_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 567 81 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 567 40 41, g32p_row17_traceSegment_030_0567_0040, g32p_row17_traceSegment_030_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_030 486 162 = [0, 8, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 486 81 81, g32p_row17_traceSegment_030_0486_0081, g32p_row17_traceSegment_030_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_030 324 324 = [0, 21, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 324 162 162, g32p_row17_traceSegment_030_0324_0162, g32p_row17_traceSegment_030_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_030 0 648 = [0, 38, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 0 324 324, g32p_row17_traceSegment_030_0000_0324, g32p_row17_traceSegment_030_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 648 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 648 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 648 10 10, g32p_row17_traceSegment_030_0648_0010, g32p_row17_traceSegment_030_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 678 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 668 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 668 10 10, g32p_row17_traceSegment_030_0668_0010, g32p_row17_traceSegment_030_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 648 40 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 648 20 20, g32p_row17_traceSegment_030_0648_0020, g32p_row17_traceSegment_030_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 688 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 688 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 688 10 10, g32p_row17_traceSegment_030_0688_0010, g32p_row17_traceSegment_030_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 708 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 718 11 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 708 21 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 708 10 11, g32p_row17_traceSegment_030_0708_0010, g32p_row17_traceSegment_030_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 688 41 = [0, 4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 688 20 21, g32p_row17_traceSegment_030_0688_0020, g32p_row17_traceSegment_030_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 648 81 = [0, 6, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 648 40 41, g32p_row17_traceSegment_030_0648_0040, g32p_row17_traceSegment_030_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 729 10 = [0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 729 20 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 729 10 10, g32p_row17_traceSegment_030_0729_0010, g32p_row17_traceSegment_030_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 749 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 749 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 749 10 10, g32p_row17_traceSegment_030_0749_0010, g32p_row17_traceSegment_030_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 729 40 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 729 20 20, g32p_row17_traceSegment_030_0729_0020, g32p_row17_traceSegment_030_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 769 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 779 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 769 20 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 769 10 10, g32p_row17_traceSegment_030_0769_0010, g32p_row17_traceSegment_030_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 799 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 789 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 789 10 11, g32p_row17_traceSegment_030_0789_0010, g32p_row17_traceSegment_030_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 769 41 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 769 20 21, g32p_row17_traceSegment_030_0769_0020, g32p_row17_traceSegment_030_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 729 81 = [0, 1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 729 40 41, g32p_row17_traceSegment_030_0729_0040, g32p_row17_traceSegment_030_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_030 648 162 = [0, 7, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 648 81 81, g32p_row17_traceSegment_030_0648_0081, g32p_row17_traceSegment_030_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 810 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 810 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 810 10 10, g32p_row17_traceSegment_030_0810_0010, g32p_row17_traceSegment_030_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 830 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 830 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 830 10 10, g32p_row17_traceSegment_030_0830_0010, g32p_row17_traceSegment_030_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 810 40 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 810 20 20, g32p_row17_traceSegment_030_0810_0020, g32p_row17_traceSegment_030_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 850 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 850 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 850 10 10, g32p_row17_traceSegment_030_0850_0010, g32p_row17_traceSegment_030_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 870 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 880 11 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 870 21 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 870 10 11, g32p_row17_traceSegment_030_0870_0010, g32p_row17_traceSegment_030_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 850 41 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 850 20 21, g32p_row17_traceSegment_030_0850_0020, g32p_row17_traceSegment_030_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 810 81 = [0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 810 40 41, g32p_row17_traceSegment_030_0810_0040, g32p_row17_traceSegment_030_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 891 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 901 10 = [0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 891 20 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 891 10 10, g32p_row17_traceSegment_030_0891_0010, g32p_row17_traceSegment_030_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 921 10 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 911 20 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 911 10 10, g32p_row17_traceSegment_030_0911_0010, g32p_row17_traceSegment_030_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 891 40 = [0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 891 20 20, g32p_row17_traceSegment_030_0891_0020, g32p_row17_traceSegment_030_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 931 10 = [0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 941 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 931 20 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 931 10 10, g32p_row17_traceSegment_030_0931_0010, g32p_row17_traceSegment_030_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 951 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 961 11 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 951 21 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 951 10 11, g32p_row17_traceSegment_030_0951_0010, g32p_row17_traceSegment_030_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 931 41 = [0, 4, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 931 20 21, g32p_row17_traceSegment_030_0931_0020, g32p_row17_traceSegment_030_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 891 81 = [0, 8, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 891 40 41, g32p_row17_traceSegment_030_0891_0040, g32p_row17_traceSegment_030_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_030 810 162 = [0, 10, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 810 81 81, g32p_row17_traceSegment_030_0810_0081, g32p_row17_traceSegment_030_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_030 648 324 = [0, 17, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 648 162 162, g32p_row17_traceSegment_030_0648_0162, g32p_row17_traceSegment_030_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 982 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 972 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 972 10 10, g32p_row17_traceSegment_030_0972_0010, g32p_row17_traceSegment_030_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 992 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 992 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 992 10 10, g32p_row17_traceSegment_030_0992_0010, g32p_row17_traceSegment_030_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 972 40 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 972 20 20, g32p_row17_traceSegment_030_0972_0020, g32p_row17_traceSegment_030_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1022 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 1012 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1012 10 10, g32p_row17_traceSegment_030_1012_0010, g32p_row17_traceSegment_030_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1032 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 1032 21 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1032 10 11, g32p_row17_traceSegment_030_1032_0010, g32p_row17_traceSegment_030_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 1012 41 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1012 20 21, g32p_row17_traceSegment_030_1012_0020, g32p_row17_traceSegment_030_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 972 81 = [0, 4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 972 40 41, g32p_row17_traceSegment_030_0972_0040, g32p_row17_traceSegment_030_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1053 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 1053 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1053 10 10, g32p_row17_traceSegment_030_1053_0010, g32p_row17_traceSegment_030_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1073 10 10, g32p_row17_traceSegment_030_1073_0010, g32p_row17_traceSegment_030_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 1053 40 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1053 20 20, g32p_row17_traceSegment_030_1053_0020, g32p_row17_traceSegment_030_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1093 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1103 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 1093 20 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1093 10 10, g32p_row17_traceSegment_030_1093_0010, g32p_row17_traceSegment_030_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1113 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 1123 11 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 1113 21 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1113 10 11, g32p_row17_traceSegment_030_1113_0010, g32p_row17_traceSegment_030_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 1093 41 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1093 20 21, g32p_row17_traceSegment_030_1093_0020, g32p_row17_traceSegment_030_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 1053 81 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1053 40 41, g32p_row17_traceSegment_030_1053_0040, g32p_row17_traceSegment_030_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_030 972 162 = [0, 12, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 972 81 81, g32p_row17_traceSegment_030_0972_0081, g32p_row17_traceSegment_030_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1144 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 1134 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1134 10 10, g32p_row17_traceSegment_030_1134_0010, g32p_row17_traceSegment_030_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1164 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 1154 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1154 10 10, g32p_row17_traceSegment_030_1154_0010, g32p_row17_traceSegment_030_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 1134 40 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1134 20 20, g32p_row17_traceSegment_030_1134_0020, g32p_row17_traceSegment_030_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1174 10 10, g32p_row17_traceSegment_030_1174_0010, g32p_row17_traceSegment_030_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 1204 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 1194 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1194 10 11, g32p_row17_traceSegment_030_1194_0010, g32p_row17_traceSegment_030_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 1174 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1174 20 21, g32p_row17_traceSegment_030_1174_0020, g32p_row17_traceSegment_030_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 1134 81 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1134 40 41, g32p_row17_traceSegment_030_1134_0040, g32p_row17_traceSegment_030_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1215 10 10, g32p_row17_traceSegment_030_1215_0010, g32p_row17_traceSegment_030_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1235 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1245 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 1235 20 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1235 10 10, g32p_row17_traceSegment_030_1235_0010, g32p_row17_traceSegment_030_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_030 1215 40 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1215 20 20, g32p_row17_traceSegment_030_1215_0020, g32p_row17_traceSegment_030_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1255 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_030 1255 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1255 10 10, g32p_row17_traceSegment_030_1255_0010, g32p_row17_traceSegment_030_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_030 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_030 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_030_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_030 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1275 10 11, g32p_row17_traceSegment_030_1275_0010, g32p_row17_traceSegment_030_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_030 1255 41 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1255 20 21, g32p_row17_traceSegment_030_1255_0020, g32p_row17_traceSegment_030_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_030 1215 81 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1215 40 41, g32p_row17_traceSegment_030_1215_0040, g32p_row17_traceSegment_030_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_030_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_030 1134 162 = [0, 5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 1134 81 81, g32p_row17_traceSegment_030_1134_0081, g32p_row17_traceSegment_030_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_030 972 324 = [0, 17, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 972 162 162, g32p_row17_traceSegment_030_0972_0162, g32p_row17_traceSegment_030_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_030 648 648 = [0, 34, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 648 324 324, g32p_row17_traceSegment_030_0648_0324, g32p_row17_traceSegment_030_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_030_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_030 0 1296 = [0, 72, 0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_030 0 648 648, g32p_row17_traceSegment_030_0000_0648, g32p_row17_traceSegment_030_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_030 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 30 = [0, 72, 0, 0, 36] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_030_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_032 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 32 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_032_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 0 10 10, g32p_row17_traceSegment_032_0000_0010, g32p_row17_traceSegment_032_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 20 10 10, g32p_row17_traceSegment_032_0020_0010, g32p_row17_traceSegment_032_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 0 20 20, g32p_row17_traceSegment_032_0000_0020, g32p_row17_traceSegment_032_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 40 10 10, g32p_row17_traceSegment_032_0040_0010, g32p_row17_traceSegment_032_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 60 10 11, g32p_row17_traceSegment_032_0060_0010, g32p_row17_traceSegment_032_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 40 20 21, g32p_row17_traceSegment_032_0040_0020, g32p_row17_traceSegment_032_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 0 40 41, g32p_row17_traceSegment_032_0000_0040, g32p_row17_traceSegment_032_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 81 10 10, g32p_row17_traceSegment_032_0081_0010, g32p_row17_traceSegment_032_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 101 10 10, g32p_row17_traceSegment_032_0101_0010, g32p_row17_traceSegment_032_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 81 20 20, g32p_row17_traceSegment_032_0081_0020, g32p_row17_traceSegment_032_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 131 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 121 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 121 10 10, g32p_row17_traceSegment_032_0121_0010, g32p_row17_traceSegment_032_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 141 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 141 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 141 10 11, g32p_row17_traceSegment_032_0141_0010, g32p_row17_traceSegment_032_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 121 41 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 121 20 21, g32p_row17_traceSegment_032_0121_0020, g32p_row17_traceSegment_032_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 81 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 81 40 41, g32p_row17_traceSegment_032_0081_0040, g32p_row17_traceSegment_032_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_032 0 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 0 81 81, g32p_row17_traceSegment_032_0000_0081, g32p_row17_traceSegment_032_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 162 10 10, g32p_row17_traceSegment_032_0162_0010, g32p_row17_traceSegment_032_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 182 10 10, g32p_row17_traceSegment_032_0182_0010, g32p_row17_traceSegment_032_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 162 20 20, g32p_row17_traceSegment_032_0162_0020, g32p_row17_traceSegment_032_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 202 10 10, g32p_row17_traceSegment_032_0202_0010, g32p_row17_traceSegment_032_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 222 10 11, g32p_row17_traceSegment_032_0222_0010, g32p_row17_traceSegment_032_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 202 20 21, g32p_row17_traceSegment_032_0202_0020, g32p_row17_traceSegment_032_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 162 40 41, g32p_row17_traceSegment_032_0162_0040, g32p_row17_traceSegment_032_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 243 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 253 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 243 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 243 10 10, g32p_row17_traceSegment_032_0243_0010, g32p_row17_traceSegment_032_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 273 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 263 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 263 10 10, g32p_row17_traceSegment_032_0263_0010, g32p_row17_traceSegment_032_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 243 40 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 243 20 20, g32p_row17_traceSegment_032_0243_0020, g32p_row17_traceSegment_032_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 283 10 10, g32p_row17_traceSegment_032_0283_0010, g32p_row17_traceSegment_032_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 303 10 11, g32p_row17_traceSegment_032_0303_0010, g32p_row17_traceSegment_032_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 283 20 21, g32p_row17_traceSegment_032_0283_0020, g32p_row17_traceSegment_032_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 243 81 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 243 40 41, g32p_row17_traceSegment_032_0243_0040, g32p_row17_traceSegment_032_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_032 162 162 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 162 81 81, g32p_row17_traceSegment_032_0162_0081, g32p_row17_traceSegment_032_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_032 0 324 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 0 162 162, g32p_row17_traceSegment_032_0000_0162, g32p_row17_traceSegment_032_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 324 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 324 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 324 10 10, g32p_row17_traceSegment_032_0324_0010, g32p_row17_traceSegment_032_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 344 10 10, g32p_row17_traceSegment_032_0344_0010, g32p_row17_traceSegment_032_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 324 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 324 20 20, g32p_row17_traceSegment_032_0324_0020, g32p_row17_traceSegment_032_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 364 10 10, g32p_row17_traceSegment_032_0364_0010, g32p_row17_traceSegment_032_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 384 10 11, g32p_row17_traceSegment_032_0384_0010, g32p_row17_traceSegment_032_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 364 20 21, g32p_row17_traceSegment_032_0364_0020, g32p_row17_traceSegment_032_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 324 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 324 40 41, g32p_row17_traceSegment_032_0324_0040, g32p_row17_traceSegment_032_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 405 10 10, g32p_row17_traceSegment_032_0405_0010, g32p_row17_traceSegment_032_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 425 10 10, g32p_row17_traceSegment_032_0425_0010, g32p_row17_traceSegment_032_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 405 20 20, g32p_row17_traceSegment_032_0405_0020, g32p_row17_traceSegment_032_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 445 10 10, g32p_row17_traceSegment_032_0445_0010, g32p_row17_traceSegment_032_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 465 10 11, g32p_row17_traceSegment_032_0465_0010, g32p_row17_traceSegment_032_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 445 20 21, g32p_row17_traceSegment_032_0445_0020, g32p_row17_traceSegment_032_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 405 40 41, g32p_row17_traceSegment_032_0405_0040, g32p_row17_traceSegment_032_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_032 324 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 324 81 81, g32p_row17_traceSegment_032_0324_0081, g32p_row17_traceSegment_032_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 486 10 10, g32p_row17_traceSegment_032_0486_0010, g32p_row17_traceSegment_032_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 506 10 10, g32p_row17_traceSegment_032_0506_0010, g32p_row17_traceSegment_032_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 486 20 20, g32p_row17_traceSegment_032_0486_0020, g32p_row17_traceSegment_032_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 526 10 10, g32p_row17_traceSegment_032_0526_0010, g32p_row17_traceSegment_032_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 546 10 11, g32p_row17_traceSegment_032_0546_0010, g32p_row17_traceSegment_032_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 526 20 21, g32p_row17_traceSegment_032_0526_0020, g32p_row17_traceSegment_032_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 486 40 41, g32p_row17_traceSegment_032_0486_0040, g32p_row17_traceSegment_032_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 567 10 10, g32p_row17_traceSegment_032_0567_0010, g32p_row17_traceSegment_032_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 587 10 10, g32p_row17_traceSegment_032_0587_0010, g32p_row17_traceSegment_032_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 567 20 20, g32p_row17_traceSegment_032_0567_0020, g32p_row17_traceSegment_032_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 607 10 10, g32p_row17_traceSegment_032_0607_0010, g32p_row17_traceSegment_032_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 627 10 11, g32p_row17_traceSegment_032_0627_0010, g32p_row17_traceSegment_032_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 607 20 21, g32p_row17_traceSegment_032_0607_0020, g32p_row17_traceSegment_032_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 567 40 41, g32p_row17_traceSegment_032_0567_0040, g32p_row17_traceSegment_032_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_032 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 486 81 81, g32p_row17_traceSegment_032_0486_0081, g32p_row17_traceSegment_032_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_032 324 324 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 324 162 162, g32p_row17_traceSegment_032_0324_0162, g32p_row17_traceSegment_032_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_032 0 648 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 0 324 324, g32p_row17_traceSegment_032_0000_0324, g32p_row17_traceSegment_032_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 648 10 10, g32p_row17_traceSegment_032_0648_0010, g32p_row17_traceSegment_032_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 668 10 10, g32p_row17_traceSegment_032_0668_0010, g32p_row17_traceSegment_032_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 648 20 20, g32p_row17_traceSegment_032_0648_0020, g32p_row17_traceSegment_032_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 688 10 10, g32p_row17_traceSegment_032_0688_0010, g32p_row17_traceSegment_032_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 708 10 11, g32p_row17_traceSegment_032_0708_0010, g32p_row17_traceSegment_032_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 688 20 21, g32p_row17_traceSegment_032_0688_0020, g32p_row17_traceSegment_032_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 648 40 41, g32p_row17_traceSegment_032_0648_0040, g32p_row17_traceSegment_032_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 729 10 10, g32p_row17_traceSegment_032_0729_0010, g32p_row17_traceSegment_032_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 749 10 10, g32p_row17_traceSegment_032_0749_0010, g32p_row17_traceSegment_032_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 729 20 20, g32p_row17_traceSegment_032_0729_0020, g32p_row17_traceSegment_032_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 769 10 10, g32p_row17_traceSegment_032_0769_0010, g32p_row17_traceSegment_032_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 789 10 11, g32p_row17_traceSegment_032_0789_0010, g32p_row17_traceSegment_032_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 769 20 21, g32p_row17_traceSegment_032_0769_0020, g32p_row17_traceSegment_032_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 729 40 41, g32p_row17_traceSegment_032_0729_0040, g32p_row17_traceSegment_032_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_032 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 648 81 81, g32p_row17_traceSegment_032_0648_0081, g32p_row17_traceSegment_032_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 810 10 10, g32p_row17_traceSegment_032_0810_0010, g32p_row17_traceSegment_032_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 830 10 10, g32p_row17_traceSegment_032_0830_0010, g32p_row17_traceSegment_032_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 810 20 20, g32p_row17_traceSegment_032_0810_0020, g32p_row17_traceSegment_032_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 850 10 10, g32p_row17_traceSegment_032_0850_0010, g32p_row17_traceSegment_032_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 870 10 11, g32p_row17_traceSegment_032_0870_0010, g32p_row17_traceSegment_032_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 850 20 21, g32p_row17_traceSegment_032_0850_0020, g32p_row17_traceSegment_032_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 810 40 41, g32p_row17_traceSegment_032_0810_0040, g32p_row17_traceSegment_032_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 891 10 10, g32p_row17_traceSegment_032_0891_0010, g32p_row17_traceSegment_032_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 911 10 10, g32p_row17_traceSegment_032_0911_0010, g32p_row17_traceSegment_032_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 891 20 20, g32p_row17_traceSegment_032_0891_0020, g32p_row17_traceSegment_032_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 931 10 10, g32p_row17_traceSegment_032_0931_0010, g32p_row17_traceSegment_032_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 951 10 11, g32p_row17_traceSegment_032_0951_0010, g32p_row17_traceSegment_032_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 931 20 21, g32p_row17_traceSegment_032_0931_0020, g32p_row17_traceSegment_032_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 891 40 41, g32p_row17_traceSegment_032_0891_0040, g32p_row17_traceSegment_032_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_032 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 810 81 81, g32p_row17_traceSegment_032_0810_0081, g32p_row17_traceSegment_032_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_032 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 648 162 162, g32p_row17_traceSegment_032_0648_0162, g32p_row17_traceSegment_032_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 972 10 10, g32p_row17_traceSegment_032_0972_0010, g32p_row17_traceSegment_032_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 992 10 10, g32p_row17_traceSegment_032_0992_0010, g32p_row17_traceSegment_032_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 972 20 20, g32p_row17_traceSegment_032_0972_0020, g32p_row17_traceSegment_032_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1012 10 10, g32p_row17_traceSegment_032_1012_0010, g32p_row17_traceSegment_032_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1032 10 11, g32p_row17_traceSegment_032_1032_0010, g32p_row17_traceSegment_032_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1012 20 21, g32p_row17_traceSegment_032_1012_0020, g32p_row17_traceSegment_032_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 972 40 41, g32p_row17_traceSegment_032_0972_0040, g32p_row17_traceSegment_032_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1053 10 10, g32p_row17_traceSegment_032_1053_0010, g32p_row17_traceSegment_032_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1073 10 10, g32p_row17_traceSegment_032_1073_0010, g32p_row17_traceSegment_032_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1053 20 20, g32p_row17_traceSegment_032_1053_0020, g32p_row17_traceSegment_032_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1103 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 1093 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1093 10 10, g32p_row17_traceSegment_032_1093_0010, g32p_row17_traceSegment_032_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 1123 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 1113 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1113 10 11, g32p_row17_traceSegment_032_1113_0010, g32p_row17_traceSegment_032_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 1093 41 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1093 20 21, g32p_row17_traceSegment_032_1093_0020, g32p_row17_traceSegment_032_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 1053 81 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1053 40 41, g32p_row17_traceSegment_032_1053_0040, g32p_row17_traceSegment_032_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_032 972 162 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 972 81 81, g32p_row17_traceSegment_032_0972_0081, g32p_row17_traceSegment_032_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1134 10 10, g32p_row17_traceSegment_032_1134_0010, g32p_row17_traceSegment_032_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1164 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 1154 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1154 10 10, g32p_row17_traceSegment_032_1154_0010, g32p_row17_traceSegment_032_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 1134 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1134 20 20, g32p_row17_traceSegment_032_1134_0020, g32p_row17_traceSegment_032_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1184 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 1174 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1174 10 10, g32p_row17_traceSegment_032_1174_0010, g32p_row17_traceSegment_032_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1194 10 11, g32p_row17_traceSegment_032_1194_0010, g32p_row17_traceSegment_032_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 1174 41 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1174 20 21, g32p_row17_traceSegment_032_1174_0020, g32p_row17_traceSegment_032_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 1134 81 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1134 40 41, g32p_row17_traceSegment_032_1134_0040, g32p_row17_traceSegment_032_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1215 10 10, g32p_row17_traceSegment_032_1215_0010, g32p_row17_traceSegment_032_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1235 10 10, g32p_row17_traceSegment_032_1235_0010, g32p_row17_traceSegment_032_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_032 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1215 20 20, g32p_row17_traceSegment_032_1215_0020, g32p_row17_traceSegment_032_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_032 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1255 10 10, g32p_row17_traceSegment_032_1255_0010, g32p_row17_traceSegment_032_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_032 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_032 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_032_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_032 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1275 10 11, g32p_row17_traceSegment_032_1275_0010, g32p_row17_traceSegment_032_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_032 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1255 20 21, g32p_row17_traceSegment_032_1255_0020, g32p_row17_traceSegment_032_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_032 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1215 40 41, g32p_row17_traceSegment_032_1215_0040, g32p_row17_traceSegment_032_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_032_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_032 1134 162 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 1134 81 81, g32p_row17_traceSegment_032_1134_0081, g32p_row17_traceSegment_032_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_032 972 324 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 972 162 162, g32p_row17_traceSegment_032_0972_0162, g32p_row17_traceSegment_032_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_032 648 648 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 648 324 324, g32p_row17_traceSegment_032_0648_0324, g32p_row17_traceSegment_032_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_032_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_032 0 1296 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_032 0 648 648, g32p_row17_traceSegment_032_0000_0648, g32p_row17_traceSegment_032_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 32 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_032_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_034 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 34 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_034_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 0 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 0 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 0 10 10, g32p_row17_traceSegment_034_0000_0010, g32p_row17_traceSegment_034_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 20 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 30 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 20 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 20 10 10, g32p_row17_traceSegment_034_0020_0010, g32p_row17_traceSegment_034_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 0 40 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 0 20 20, g32p_row17_traceSegment_034_0000_0020, g32p_row17_traceSegment_034_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 50 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 40 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 40 10 10, g32p_row17_traceSegment_034_0040_0010, g32p_row17_traceSegment_034_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 70 11 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 60 21 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 60 10 11, g32p_row17_traceSegment_034_0060_0010, g32p_row17_traceSegment_034_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 40 41 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 40 20 21, g32p_row17_traceSegment_034_0040_0020, g32p_row17_traceSegment_034_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 0 81 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 0 40 41, g32p_row17_traceSegment_034_0000_0040, g32p_row17_traceSegment_034_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 81 10 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 81 20 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 81 10 10, g32p_row17_traceSegment_034_0081_0010, g32p_row17_traceSegment_034_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 101 10 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 111 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 101 20 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 101 10 10, g32p_row17_traceSegment_034_0101_0010, g32p_row17_traceSegment_034_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 81 40 = [0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 81 20 20, g32p_row17_traceSegment_034_0081_0020, g32p_row17_traceSegment_034_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 121 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 121 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 121 10 10, g32p_row17_traceSegment_034_0121_0010, g32p_row17_traceSegment_034_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 141 10 11, g32p_row17_traceSegment_034_0141_0010, g32p_row17_traceSegment_034_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 121 41 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 121 20 21, g32p_row17_traceSegment_034_0121_0020, g32p_row17_traceSegment_034_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 81 81 = [0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 81 40 41, g32p_row17_traceSegment_034_0081_0040, g32p_row17_traceSegment_034_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_034 0 162 = [0, 9, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 0 81 81, g32p_row17_traceSegment_034_0000_0081, g32p_row17_traceSegment_034_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 172 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 162 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 162 10 10, g32p_row17_traceSegment_034_0162_0010, g32p_row17_traceSegment_034_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 182 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 192 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 182 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 182 10 10, g32p_row17_traceSegment_034_0182_0010, g32p_row17_traceSegment_034_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 162 40 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 162 20 20, g32p_row17_traceSegment_034_0162_0020, g32p_row17_traceSegment_034_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 202 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 202 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 202 10 10, g32p_row17_traceSegment_034_0202_0010, g32p_row17_traceSegment_034_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 222 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 222 21 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 222 10 11, g32p_row17_traceSegment_034_0222_0010, g32p_row17_traceSegment_034_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 202 41 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 202 20 21, g32p_row17_traceSegment_034_0202_0020, g32p_row17_traceSegment_034_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 162 81 = [0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 162 40 41, g32p_row17_traceSegment_034_0162_0040, g32p_row17_traceSegment_034_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 253 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 243 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 243 10 10, g32p_row17_traceSegment_034_0243_0010, g32p_row17_traceSegment_034_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 263 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 263 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 263 10 10, g32p_row17_traceSegment_034_0263_0010, g32p_row17_traceSegment_034_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 243 40 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 243 20 20, g32p_row17_traceSegment_034_0243_0020, g32p_row17_traceSegment_034_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 283 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 283 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 283 10 10, g32p_row17_traceSegment_034_0283_0010, g32p_row17_traceSegment_034_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 303 10 11, g32p_row17_traceSegment_034_0303_0010, g32p_row17_traceSegment_034_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 283 41 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 283 20 21, g32p_row17_traceSegment_034_0283_0020, g32p_row17_traceSegment_034_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 243 81 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 243 40 41, g32p_row17_traceSegment_034_0243_0040, g32p_row17_traceSegment_034_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_034 162 162 = [0, 5, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 162 81 81, g32p_row17_traceSegment_034_0162_0081, g32p_row17_traceSegment_034_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_034 0 324 = [0, 14, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 0 162 162, g32p_row17_traceSegment_034_0000_0162, g32p_row17_traceSegment_034_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 334 10 = [0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 324 20 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 324 10 10, g32p_row17_traceSegment_034_0324_0010, g32p_row17_traceSegment_034_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 354 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 344 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 344 10 10, g32p_row17_traceSegment_034_0344_0010, g32p_row17_traceSegment_034_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 324 40 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 324 20 20, g32p_row17_traceSegment_034_0324_0020, g32p_row17_traceSegment_034_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 374 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 364 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 364 10 10, g32p_row17_traceSegment_034_0364_0010, g32p_row17_traceSegment_034_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 384 10 11, g32p_row17_traceSegment_034_0384_0010, g32p_row17_traceSegment_034_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 364 41 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 364 20 21, g32p_row17_traceSegment_034_0364_0020, g32p_row17_traceSegment_034_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 324 81 = [0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 324 40 41, g32p_row17_traceSegment_034_0324_0040, g32p_row17_traceSegment_034_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 405 10 10, g32p_row17_traceSegment_034_0405_0010, g32p_row17_traceSegment_034_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 425 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 425 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 425 10 10, g32p_row17_traceSegment_034_0425_0010, g32p_row17_traceSegment_034_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 405 40 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 405 20 20, g32p_row17_traceSegment_034_0405_0020, g32p_row17_traceSegment_034_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 445 10 10, g32p_row17_traceSegment_034_0445_0010, g32p_row17_traceSegment_034_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 465 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 465 21 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 465 10 11, g32p_row17_traceSegment_034_0465_0010, g32p_row17_traceSegment_034_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 445 41 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 445 20 21, g32p_row17_traceSegment_034_0445_0020, g32p_row17_traceSegment_034_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 405 81 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 405 40 41, g32p_row17_traceSegment_034_0405_0040, g32p_row17_traceSegment_034_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_034 324 162 = [0, 4, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 324 81 81, g32p_row17_traceSegment_034_0324_0081, g32p_row17_traceSegment_034_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 486 10 10, g32p_row17_traceSegment_034_0486_0010, g32p_row17_traceSegment_034_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 506 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 506 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 506 10 10, g32p_row17_traceSegment_034_0506_0010, g32p_row17_traceSegment_034_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 486 40 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 486 20 20, g32p_row17_traceSegment_034_0486_0020, g32p_row17_traceSegment_034_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 526 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 536 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 526 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 526 10 10, g32p_row17_traceSegment_034_0526_0010, g32p_row17_traceSegment_034_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 546 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 546 21 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 546 10 11, g32p_row17_traceSegment_034_0546_0010, g32p_row17_traceSegment_034_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 526 41 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 526 20 21, g32p_row17_traceSegment_034_0526_0020, g32p_row17_traceSegment_034_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 486 81 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 486 40 41, g32p_row17_traceSegment_034_0486_0040, g32p_row17_traceSegment_034_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 577 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 567 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 567 10 10, g32p_row17_traceSegment_034_0567_0010, g32p_row17_traceSegment_034_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 587 10 10, g32p_row17_traceSegment_034_0587_0010, g32p_row17_traceSegment_034_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 567 40 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 567 20 20, g32p_row17_traceSegment_034_0567_0020, g32p_row17_traceSegment_034_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 607 10 10, g32p_row17_traceSegment_034_0607_0010, g32p_row17_traceSegment_034_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 627 10 11, g32p_row17_traceSegment_034_0627_0010, g32p_row17_traceSegment_034_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 607 20 21, g32p_row17_traceSegment_034_0607_0020, g32p_row17_traceSegment_034_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 567 81 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 567 40 41, g32p_row17_traceSegment_034_0567_0040, g32p_row17_traceSegment_034_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_034 486 162 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 486 81 81, g32p_row17_traceSegment_034_0486_0081, g32p_row17_traceSegment_034_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_034 324 324 = [0, 9, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 324 162 162, g32p_row17_traceSegment_034_0324_0162, g32p_row17_traceSegment_034_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_034 0 648 = [0, 23, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 0 324 324, g32p_row17_traceSegment_034_0000_0324, g32p_row17_traceSegment_034_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 648 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 648 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 648 10 10, g32p_row17_traceSegment_034_0648_0010, g32p_row17_traceSegment_034_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 678 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 668 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 668 10 10, g32p_row17_traceSegment_034_0668_0010, g32p_row17_traceSegment_034_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 648 40 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 648 20 20, g32p_row17_traceSegment_034_0648_0020, g32p_row17_traceSegment_034_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 688 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 698 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 688 20 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 688 10 10, g32p_row17_traceSegment_034_0688_0010, g32p_row17_traceSegment_034_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 708 10 11, g32p_row17_traceSegment_034_0708_0010, g32p_row17_traceSegment_034_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 688 41 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 688 20 21, g32p_row17_traceSegment_034_0688_0020, g32p_row17_traceSegment_034_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 648 81 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 648 40 41, g32p_row17_traceSegment_034_0648_0040, g32p_row17_traceSegment_034_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 729 10 10, g32p_row17_traceSegment_034_0729_0010, g32p_row17_traceSegment_034_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 749 10 10, g32p_row17_traceSegment_034_0749_0010, g32p_row17_traceSegment_034_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 729 20 20, g32p_row17_traceSegment_034_0729_0020, g32p_row17_traceSegment_034_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 769 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 779 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 769 20 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 769 10 10, g32p_row17_traceSegment_034_0769_0010, g32p_row17_traceSegment_034_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 799 11 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 789 21 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 789 10 11, g32p_row17_traceSegment_034_0789_0010, g32p_row17_traceSegment_034_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 769 41 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 769 20 21, g32p_row17_traceSegment_034_0769_0020, g32p_row17_traceSegment_034_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 729 81 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 729 40 41, g32p_row17_traceSegment_034_0729_0040, g32p_row17_traceSegment_034_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_034 648 162 = [0, 5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 648 81 81, g32p_row17_traceSegment_034_0648_0081, g32p_row17_traceSegment_034_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 810 10 10, g32p_row17_traceSegment_034_0810_0010, g32p_row17_traceSegment_034_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 840 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 830 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 830 10 10, g32p_row17_traceSegment_034_0830_0010, g32p_row17_traceSegment_034_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 810 40 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 810 20 20, g32p_row17_traceSegment_034_0810_0020, g32p_row17_traceSegment_034_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 850 10 10, g32p_row17_traceSegment_034_0850_0010, g32p_row17_traceSegment_034_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 870 10 11, g32p_row17_traceSegment_034_0870_0010, g32p_row17_traceSegment_034_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 850 20 21, g32p_row17_traceSegment_034_0850_0020, g32p_row17_traceSegment_034_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 810 81 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 810 40 41, g32p_row17_traceSegment_034_0810_0040, g32p_row17_traceSegment_034_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 901 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 891 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 891 10 10, g32p_row17_traceSegment_034_0891_0010, g32p_row17_traceSegment_034_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 921 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 911 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 911 10 10, g32p_row17_traceSegment_034_0911_0010, g32p_row17_traceSegment_034_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 891 40 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 891 20 20, g32p_row17_traceSegment_034_0891_0020, g32p_row17_traceSegment_034_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 931 10 10, g32p_row17_traceSegment_034_0931_0010, g32p_row17_traceSegment_034_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 951 10 11, g32p_row17_traceSegment_034_0951_0010, g32p_row17_traceSegment_034_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 931 20 21, g32p_row17_traceSegment_034_0931_0020, g32p_row17_traceSegment_034_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 891 81 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 891 40 41, g32p_row17_traceSegment_034_0891_0040, g32p_row17_traceSegment_034_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_034 810 162 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 810 81 81, g32p_row17_traceSegment_034_0810_0081, g32p_row17_traceSegment_034_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_034 648 324 = [0, 8, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 648 162 162, g32p_row17_traceSegment_034_0648_0162, g32p_row17_traceSegment_034_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 972 10 10, g32p_row17_traceSegment_034_0972_0010, g32p_row17_traceSegment_034_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 992 10 10, g32p_row17_traceSegment_034_0992_0010, g32p_row17_traceSegment_034_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 972 20 20, g32p_row17_traceSegment_034_0972_0020, g32p_row17_traceSegment_034_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1012 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1022 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 1012 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1012 10 10, g32p_row17_traceSegment_034_1012_0010, g32p_row17_traceSegment_034_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1032 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 1032 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1032 10 11, g32p_row17_traceSegment_034_1032_0010, g32p_row17_traceSegment_034_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 1012 41 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1012 20 21, g32p_row17_traceSegment_034_1012_0020, g32p_row17_traceSegment_034_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 972 81 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 972 40 41, g32p_row17_traceSegment_034_0972_0040, g32p_row17_traceSegment_034_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1053 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 1053 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1053 10 10, g32p_row17_traceSegment_034_1053_0010, g32p_row17_traceSegment_034_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1073 10 10, g32p_row17_traceSegment_034_1073_0010, g32p_row17_traceSegment_034_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 1053 40 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1053 20 20, g32p_row17_traceSegment_034_1053_0020, g32p_row17_traceSegment_034_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1093 10 10, g32p_row17_traceSegment_034_1093_0010, g32p_row17_traceSegment_034_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1113 10 11, g32p_row17_traceSegment_034_1113_0010, g32p_row17_traceSegment_034_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1093 20 21, g32p_row17_traceSegment_034_1093_0020, g32p_row17_traceSegment_034_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 1053 81 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1053 40 41, g32p_row17_traceSegment_034_1053_0040, g32p_row17_traceSegment_034_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_034 972 162 = [0, 4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 972 81 81, g32p_row17_traceSegment_034_0972_0081, g32p_row17_traceSegment_034_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1144 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 1134 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1134 10 10, g32p_row17_traceSegment_034_1134_0010, g32p_row17_traceSegment_034_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1154 10 10, g32p_row17_traceSegment_034_1154_0010, g32p_row17_traceSegment_034_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 1134 40 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1134 20 20, g32p_row17_traceSegment_034_1134_0020, g32p_row17_traceSegment_034_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1174 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 1174 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1174 10 10, g32p_row17_traceSegment_034_1174_0010, g32p_row17_traceSegment_034_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 1204 11 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 1194 21 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1194 10 11, g32p_row17_traceSegment_034_1194_0010, g32p_row17_traceSegment_034_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 1174 41 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1174 20 21, g32p_row17_traceSegment_034_1174_0020, g32p_row17_traceSegment_034_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 1134 81 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1134 40 41, g32p_row17_traceSegment_034_1134_0040, g32p_row17_traceSegment_034_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1225 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 1215 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1215 10 10, g32p_row17_traceSegment_034_1215_0010, g32p_row17_traceSegment_034_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1235 10 10, g32p_row17_traceSegment_034_1235_0010, g32p_row17_traceSegment_034_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_034 1215 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1215 20 20, g32p_row17_traceSegment_034_1215_0020, g32p_row17_traceSegment_034_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_034 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1255 10 10, g32p_row17_traceSegment_034_1255_0010, g32p_row17_traceSegment_034_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_034 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_034 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_034_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_034 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1275 10 11, g32p_row17_traceSegment_034_1275_0010, g32p_row17_traceSegment_034_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_034 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1255 20 21, g32p_row17_traceSegment_034_1255_0020, g32p_row17_traceSegment_034_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_034 1215 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1215 40 41, g32p_row17_traceSegment_034_1215_0040, g32p_row17_traceSegment_034_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_034_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_034 1134 162 = [0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 1134 81 81, g32p_row17_traceSegment_034_1134_0081, g32p_row17_traceSegment_034_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_034 972 324 = [0, 5, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 972 162 162, g32p_row17_traceSegment_034_0972_0162, g32p_row17_traceSegment_034_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_034 648 648 = [0, 13, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 648 324 324, g32p_row17_traceSegment_034_0648_0324, g32p_row17_traceSegment_034_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_034_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_034 0 1296 = [0, 36, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_034 0 648 648, g32p_row17_traceSegment_034_0000_0648, g32p_row17_traceSegment_034_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 34 = [0, 36, 0, 0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_034_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_035 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 35 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_035_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 10 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 0 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 0 10 10, g32p_row17_traceSegment_035_0000_0010, g32p_row17_traceSegment_035_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 20 10 10, g32p_row17_traceSegment_035_0020_0010, g32p_row17_traceSegment_035_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 0 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 0 20 20, g32p_row17_traceSegment_035_0000_0020, g32p_row17_traceSegment_035_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 40 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 40 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 40 10 10, g32p_row17_traceSegment_035_0040_0010, g32p_row17_traceSegment_035_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 60 10 11, g32p_row17_traceSegment_035_0060_0010, g32p_row17_traceSegment_035_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 40 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 40 20 21, g32p_row17_traceSegment_035_0040_0020, g32p_row17_traceSegment_035_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 0 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 0 40 41, g32p_row17_traceSegment_035_0000_0040, g32p_row17_traceSegment_035_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 81 10 10, g32p_row17_traceSegment_035_0081_0010, g32p_row17_traceSegment_035_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 101 10 10, g32p_row17_traceSegment_035_0101_0010, g32p_row17_traceSegment_035_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 81 20 20, g32p_row17_traceSegment_035_0081_0020, g32p_row17_traceSegment_035_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 121 10 10, g32p_row17_traceSegment_035_0121_0010, g32p_row17_traceSegment_035_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 141 10 11, g32p_row17_traceSegment_035_0141_0010, g32p_row17_traceSegment_035_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 121 20 21, g32p_row17_traceSegment_035_0121_0020, g32p_row17_traceSegment_035_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 81 40 41, g32p_row17_traceSegment_035_0081_0040, g32p_row17_traceSegment_035_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_035 0 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 0 81 81, g32p_row17_traceSegment_035_0000_0081, g32p_row17_traceSegment_035_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 162 10 10, g32p_row17_traceSegment_035_0162_0010, g32p_row17_traceSegment_035_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 182 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 182 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 182 10 10, g32p_row17_traceSegment_035_0182_0010, g32p_row17_traceSegment_035_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 162 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 162 20 20, g32p_row17_traceSegment_035_0162_0020, g32p_row17_traceSegment_035_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 202 10 10, g32p_row17_traceSegment_035_0202_0010, g32p_row17_traceSegment_035_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 222 10 11, g32p_row17_traceSegment_035_0222_0010, g32p_row17_traceSegment_035_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 202 20 21, g32p_row17_traceSegment_035_0202_0020, g32p_row17_traceSegment_035_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 162 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 162 40 41, g32p_row17_traceSegment_035_0162_0040, g32p_row17_traceSegment_035_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 243 10 10, g32p_row17_traceSegment_035_0243_0010, g32p_row17_traceSegment_035_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 263 10 10, g32p_row17_traceSegment_035_0263_0010, g32p_row17_traceSegment_035_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 243 20 20, g32p_row17_traceSegment_035_0243_0020, g32p_row17_traceSegment_035_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 283 10 10, g32p_row17_traceSegment_035_0283_0010, g32p_row17_traceSegment_035_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 303 10 11, g32p_row17_traceSegment_035_0303_0010, g32p_row17_traceSegment_035_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 283 20 21, g32p_row17_traceSegment_035_0283_0020, g32p_row17_traceSegment_035_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 243 40 41, g32p_row17_traceSegment_035_0243_0040, g32p_row17_traceSegment_035_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_035 162 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 162 81 81, g32p_row17_traceSegment_035_0162_0081, g32p_row17_traceSegment_035_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_035 0 324 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 0 162 162, g32p_row17_traceSegment_035_0000_0162, g32p_row17_traceSegment_035_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 324 10 10, g32p_row17_traceSegment_035_0324_0010, g32p_row17_traceSegment_035_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 344 10 10, g32p_row17_traceSegment_035_0344_0010, g32p_row17_traceSegment_035_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 324 20 20, g32p_row17_traceSegment_035_0324_0020, g32p_row17_traceSegment_035_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 364 10 10, g32p_row17_traceSegment_035_0364_0010, g32p_row17_traceSegment_035_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 384 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 384 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 384 10 11, g32p_row17_traceSegment_035_0384_0010, g32p_row17_traceSegment_035_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 364 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 364 20 21, g32p_row17_traceSegment_035_0364_0020, g32p_row17_traceSegment_035_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 324 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 324 40 41, g32p_row17_traceSegment_035_0324_0040, g32p_row17_traceSegment_035_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 405 10 10, g32p_row17_traceSegment_035_0405_0010, g32p_row17_traceSegment_035_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 425 10 10, g32p_row17_traceSegment_035_0425_0010, g32p_row17_traceSegment_035_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 405 20 20, g32p_row17_traceSegment_035_0405_0020, g32p_row17_traceSegment_035_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 445 10 10, g32p_row17_traceSegment_035_0445_0010, g32p_row17_traceSegment_035_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 465 10 11, g32p_row17_traceSegment_035_0465_0010, g32p_row17_traceSegment_035_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 445 20 21, g32p_row17_traceSegment_035_0445_0020, g32p_row17_traceSegment_035_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 405 40 41, g32p_row17_traceSegment_035_0405_0040, g32p_row17_traceSegment_035_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_035 324 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 324 81 81, g32p_row17_traceSegment_035_0324_0081, g32p_row17_traceSegment_035_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 486 10 10, g32p_row17_traceSegment_035_0486_0010, g32p_row17_traceSegment_035_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 506 10 10, g32p_row17_traceSegment_035_0506_0010, g32p_row17_traceSegment_035_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 486 20 20, g32p_row17_traceSegment_035_0486_0020, g32p_row17_traceSegment_035_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 526 10 10, g32p_row17_traceSegment_035_0526_0010, g32p_row17_traceSegment_035_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 546 10 11, g32p_row17_traceSegment_035_0546_0010, g32p_row17_traceSegment_035_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 526 20 21, g32p_row17_traceSegment_035_0526_0020, g32p_row17_traceSegment_035_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 486 40 41, g32p_row17_traceSegment_035_0486_0040, g32p_row17_traceSegment_035_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 567 10 10, g32p_row17_traceSegment_035_0567_0010, g32p_row17_traceSegment_035_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 587 10 10, g32p_row17_traceSegment_035_0587_0010, g32p_row17_traceSegment_035_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 567 20 20, g32p_row17_traceSegment_035_0567_0020, g32p_row17_traceSegment_035_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 617 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 607 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 607 10 10, g32p_row17_traceSegment_035_0607_0010, g32p_row17_traceSegment_035_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 627 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 627 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 627 10 11, g32p_row17_traceSegment_035_0627_0010, g32p_row17_traceSegment_035_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 607 41 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 607 20 21, g32p_row17_traceSegment_035_0607_0020, g32p_row17_traceSegment_035_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 567 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 567 40 41, g32p_row17_traceSegment_035_0567_0040, g32p_row17_traceSegment_035_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_035 486 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 486 81 81, g32p_row17_traceSegment_035_0486_0081, g32p_row17_traceSegment_035_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_035 324 324 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 324 162 162, g32p_row17_traceSegment_035_0324_0162, g32p_row17_traceSegment_035_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_035 0 648 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 0 324 324, g32p_row17_traceSegment_035_0000_0324, g32p_row17_traceSegment_035_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 648 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 648 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 648 10 10, g32p_row17_traceSegment_035_0648_0010, g32p_row17_traceSegment_035_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 668 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 668 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 668 10 10, g32p_row17_traceSegment_035_0668_0010, g32p_row17_traceSegment_035_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 648 40 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 648 20 20, g32p_row17_traceSegment_035_0648_0020, g32p_row17_traceSegment_035_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 688 10 10, g32p_row17_traceSegment_035_0688_0010, g32p_row17_traceSegment_035_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 708 10 11, g32p_row17_traceSegment_035_0708_0010, g32p_row17_traceSegment_035_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 688 20 21, g32p_row17_traceSegment_035_0688_0020, g32p_row17_traceSegment_035_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 648 81 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 648 40 41, g32p_row17_traceSegment_035_0648_0040, g32p_row17_traceSegment_035_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 729 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 729 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 729 10 10, g32p_row17_traceSegment_035_0729_0010, g32p_row17_traceSegment_035_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 749 10 10, g32p_row17_traceSegment_035_0749_0010, g32p_row17_traceSegment_035_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 729 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 729 20 20, g32p_row17_traceSegment_035_0729_0020, g32p_row17_traceSegment_035_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 769 10 10, g32p_row17_traceSegment_035_0769_0010, g32p_row17_traceSegment_035_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 789 10 11, g32p_row17_traceSegment_035_0789_0010, g32p_row17_traceSegment_035_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 769 20 21, g32p_row17_traceSegment_035_0769_0020, g32p_row17_traceSegment_035_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 729 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 729 40 41, g32p_row17_traceSegment_035_0729_0040, g32p_row17_traceSegment_035_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_035 648 162 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 648 81 81, g32p_row17_traceSegment_035_0648_0081, g32p_row17_traceSegment_035_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 810 10 10, g32p_row17_traceSegment_035_0810_0010, g32p_row17_traceSegment_035_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 830 10 10, g32p_row17_traceSegment_035_0830_0010, g32p_row17_traceSegment_035_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 810 20 20, g32p_row17_traceSegment_035_0810_0020, g32p_row17_traceSegment_035_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 850 10 10, g32p_row17_traceSegment_035_0850_0010, g32p_row17_traceSegment_035_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 870 10 11, g32p_row17_traceSegment_035_0870_0010, g32p_row17_traceSegment_035_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 850 20 21, g32p_row17_traceSegment_035_0850_0020, g32p_row17_traceSegment_035_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 810 40 41, g32p_row17_traceSegment_035_0810_0040, g32p_row17_traceSegment_035_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 891 10 10, g32p_row17_traceSegment_035_0891_0010, g32p_row17_traceSegment_035_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 911 10 10, g32p_row17_traceSegment_035_0911_0010, g32p_row17_traceSegment_035_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 891 20 20, g32p_row17_traceSegment_035_0891_0020, g32p_row17_traceSegment_035_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 931 10 10, g32p_row17_traceSegment_035_0931_0010, g32p_row17_traceSegment_035_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 951 10 11, g32p_row17_traceSegment_035_0951_0010, g32p_row17_traceSegment_035_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 931 20 21, g32p_row17_traceSegment_035_0931_0020, g32p_row17_traceSegment_035_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 891 40 41, g32p_row17_traceSegment_035_0891_0040, g32p_row17_traceSegment_035_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_035 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 810 81 81, g32p_row17_traceSegment_035_0810_0081, g32p_row17_traceSegment_035_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_035 648 324 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 648 162 162, g32p_row17_traceSegment_035_0648_0162, g32p_row17_traceSegment_035_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 972 10 10, g32p_row17_traceSegment_035_0972_0010, g32p_row17_traceSegment_035_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 992 10 10, g32p_row17_traceSegment_035_0992_0010, g32p_row17_traceSegment_035_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 972 20 20, g32p_row17_traceSegment_035_0972_0020, g32p_row17_traceSegment_035_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1012 10 10, g32p_row17_traceSegment_035_1012_0010, g32p_row17_traceSegment_035_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 1042 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 1032 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1032 10 11, g32p_row17_traceSegment_035_1032_0010, g32p_row17_traceSegment_035_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 1012 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1012 20 21, g32p_row17_traceSegment_035_1012_0020, g32p_row17_traceSegment_035_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 972 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 972 40 41, g32p_row17_traceSegment_035_0972_0040, g32p_row17_traceSegment_035_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1053 10 10, g32p_row17_traceSegment_035_1053_0010, g32p_row17_traceSegment_035_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1073 10 10, g32p_row17_traceSegment_035_1073_0010, g32p_row17_traceSegment_035_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1053 20 20, g32p_row17_traceSegment_035_1053_0020, g32p_row17_traceSegment_035_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1093 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 1093 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1093 10 10, g32p_row17_traceSegment_035_1093_0010, g32p_row17_traceSegment_035_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1113 10 11, g32p_row17_traceSegment_035_1113_0010, g32p_row17_traceSegment_035_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 1093 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1093 20 21, g32p_row17_traceSegment_035_1093_0020, g32p_row17_traceSegment_035_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 1053 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1053 40 41, g32p_row17_traceSegment_035_1053_0040, g32p_row17_traceSegment_035_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_035 972 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 972 81 81, g32p_row17_traceSegment_035_0972_0081, g32p_row17_traceSegment_035_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1134 10 10, g32p_row17_traceSegment_035_1134_0010, g32p_row17_traceSegment_035_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1154 10 10, g32p_row17_traceSegment_035_1154_0010, g32p_row17_traceSegment_035_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1134 20 20, g32p_row17_traceSegment_035_1134_0020, g32p_row17_traceSegment_035_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1174 10 10, g32p_row17_traceSegment_035_1174_0010, g32p_row17_traceSegment_035_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1194 10 11, g32p_row17_traceSegment_035_1194_0010, g32p_row17_traceSegment_035_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1174 20 21, g32p_row17_traceSegment_035_1174_0020, g32p_row17_traceSegment_035_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1134 40 41, g32p_row17_traceSegment_035_1134_0040, g32p_row17_traceSegment_035_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1215 10 10, g32p_row17_traceSegment_035_1215_0010, g32p_row17_traceSegment_035_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1235 10 10, g32p_row17_traceSegment_035_1235_0010, g32p_row17_traceSegment_035_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_035 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1215 20 20, g32p_row17_traceSegment_035_1215_0020, g32p_row17_traceSegment_035_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_035 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1255 10 10, g32p_row17_traceSegment_035_1255_0010, g32p_row17_traceSegment_035_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_035 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_035 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_035_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_035 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1275 10 11, g32p_row17_traceSegment_035_1275_0010, g32p_row17_traceSegment_035_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_035 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1255 20 21, g32p_row17_traceSegment_035_1255_0020, g32p_row17_traceSegment_035_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_035 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1215 40 41, g32p_row17_traceSegment_035_1215_0040, g32p_row17_traceSegment_035_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_035_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_035 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 1134 81 81, g32p_row17_traceSegment_035_1134_0081, g32p_row17_traceSegment_035_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_035 972 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 972 162 162, g32p_row17_traceSegment_035_0972_0162, g32p_row17_traceSegment_035_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_035 648 648 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 648 324 324, g32p_row17_traceSegment_035_0648_0324, g32p_row17_traceSegment_035_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_035_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_035 0 1296 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_035 0 648 648, g32p_row17_traceSegment_035_0000_0648, g32p_row17_traceSegment_035_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 35 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_035_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_037 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 37 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_037_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 0 10 10, g32p_row17_traceSegment_037_0000_0010, g32p_row17_traceSegment_037_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 20 10 10, g32p_row17_traceSegment_037_0020_0010, g32p_row17_traceSegment_037_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 0 20 20, g32p_row17_traceSegment_037_0000_0020, g32p_row17_traceSegment_037_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 40 10 10, g32p_row17_traceSegment_037_0040_0010, g32p_row17_traceSegment_037_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 60 10 11, g32p_row17_traceSegment_037_0060_0010, g32p_row17_traceSegment_037_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 40 20 21, g32p_row17_traceSegment_037_0040_0020, g32p_row17_traceSegment_037_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 0 40 41, g32p_row17_traceSegment_037_0000_0040, g32p_row17_traceSegment_037_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 81 10 10, g32p_row17_traceSegment_037_0081_0010, g32p_row17_traceSegment_037_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 101 10 10, g32p_row17_traceSegment_037_0101_0010, g32p_row17_traceSegment_037_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 81 20 20, g32p_row17_traceSegment_037_0081_0020, g32p_row17_traceSegment_037_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 121 10 10, g32p_row17_traceSegment_037_0121_0010, g32p_row17_traceSegment_037_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 141 10 11, g32p_row17_traceSegment_037_0141_0010, g32p_row17_traceSegment_037_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 121 20 21, g32p_row17_traceSegment_037_0121_0020, g32p_row17_traceSegment_037_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 81 40 41, g32p_row17_traceSegment_037_0081_0040, g32p_row17_traceSegment_037_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_037 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 0 81 81, g32p_row17_traceSegment_037_0000_0081, g32p_row17_traceSegment_037_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 162 10 10, g32p_row17_traceSegment_037_0162_0010, g32p_row17_traceSegment_037_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 182 10 10, g32p_row17_traceSegment_037_0182_0010, g32p_row17_traceSegment_037_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 162 20 20, g32p_row17_traceSegment_037_0162_0020, g32p_row17_traceSegment_037_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 202 10 10, g32p_row17_traceSegment_037_0202_0010, g32p_row17_traceSegment_037_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 222 10 11, g32p_row17_traceSegment_037_0222_0010, g32p_row17_traceSegment_037_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 202 20 21, g32p_row17_traceSegment_037_0202_0020, g32p_row17_traceSegment_037_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 162 40 41, g32p_row17_traceSegment_037_0162_0040, g32p_row17_traceSegment_037_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 243 10 10, g32p_row17_traceSegment_037_0243_0010, g32p_row17_traceSegment_037_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 263 10 10, g32p_row17_traceSegment_037_0263_0010, g32p_row17_traceSegment_037_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 243 20 20, g32p_row17_traceSegment_037_0243_0020, g32p_row17_traceSegment_037_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 283 10 10, g32p_row17_traceSegment_037_0283_0010, g32p_row17_traceSegment_037_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 303 10 11, g32p_row17_traceSegment_037_0303_0010, g32p_row17_traceSegment_037_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 283 20 21, g32p_row17_traceSegment_037_0283_0020, g32p_row17_traceSegment_037_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 243 40 41, g32p_row17_traceSegment_037_0243_0040, g32p_row17_traceSegment_037_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_037 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 162 81 81, g32p_row17_traceSegment_037_0162_0081, g32p_row17_traceSegment_037_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_037 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 0 162 162, g32p_row17_traceSegment_037_0000_0162, g32p_row17_traceSegment_037_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 324 10 10, g32p_row17_traceSegment_037_0324_0010, g32p_row17_traceSegment_037_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 344 10 10, g32p_row17_traceSegment_037_0344_0010, g32p_row17_traceSegment_037_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 324 20 20, g32p_row17_traceSegment_037_0324_0020, g32p_row17_traceSegment_037_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 364 10 10, g32p_row17_traceSegment_037_0364_0010, g32p_row17_traceSegment_037_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 384 10 11, g32p_row17_traceSegment_037_0384_0010, g32p_row17_traceSegment_037_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 364 20 21, g32p_row17_traceSegment_037_0364_0020, g32p_row17_traceSegment_037_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 324 40 41, g32p_row17_traceSegment_037_0324_0040, g32p_row17_traceSegment_037_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 405 10 10, g32p_row17_traceSegment_037_0405_0010, g32p_row17_traceSegment_037_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 425 10 10, g32p_row17_traceSegment_037_0425_0010, g32p_row17_traceSegment_037_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 405 20 20, g32p_row17_traceSegment_037_0405_0020, g32p_row17_traceSegment_037_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 445 10 10, g32p_row17_traceSegment_037_0445_0010, g32p_row17_traceSegment_037_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 465 10 11, g32p_row17_traceSegment_037_0465_0010, g32p_row17_traceSegment_037_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 445 20 21, g32p_row17_traceSegment_037_0445_0020, g32p_row17_traceSegment_037_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 405 40 41, g32p_row17_traceSegment_037_0405_0040, g32p_row17_traceSegment_037_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_037 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 324 81 81, g32p_row17_traceSegment_037_0324_0081, g32p_row17_traceSegment_037_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 486 10 10, g32p_row17_traceSegment_037_0486_0010, g32p_row17_traceSegment_037_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 506 10 10, g32p_row17_traceSegment_037_0506_0010, g32p_row17_traceSegment_037_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 486 20 20, g32p_row17_traceSegment_037_0486_0020, g32p_row17_traceSegment_037_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 526 10 10, g32p_row17_traceSegment_037_0526_0010, g32p_row17_traceSegment_037_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 546 10 11, g32p_row17_traceSegment_037_0546_0010, g32p_row17_traceSegment_037_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 526 20 21, g32p_row17_traceSegment_037_0526_0020, g32p_row17_traceSegment_037_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 486 40 41, g32p_row17_traceSegment_037_0486_0040, g32p_row17_traceSegment_037_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 567 10 10, g32p_row17_traceSegment_037_0567_0010, g32p_row17_traceSegment_037_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 587 10 10, g32p_row17_traceSegment_037_0587_0010, g32p_row17_traceSegment_037_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 567 20 20, g32p_row17_traceSegment_037_0567_0020, g32p_row17_traceSegment_037_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 607 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 607 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 607 10 10, g32p_row17_traceSegment_037_0607_0010, g32p_row17_traceSegment_037_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 627 10 11, g32p_row17_traceSegment_037_0627_0010, g32p_row17_traceSegment_037_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 607 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 607 20 21, g32p_row17_traceSegment_037_0607_0020, g32p_row17_traceSegment_037_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 567 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 567 40 41, g32p_row17_traceSegment_037_0567_0040, g32p_row17_traceSegment_037_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_037 486 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 486 81 81, g32p_row17_traceSegment_037_0486_0081, g32p_row17_traceSegment_037_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_037 324 324 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 324 162 162, g32p_row17_traceSegment_037_0324_0162, g32p_row17_traceSegment_037_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_037 0 648 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 0 324 324, g32p_row17_traceSegment_037_0000_0324, g32p_row17_traceSegment_037_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 648 10 10, g32p_row17_traceSegment_037_0648_0010, g32p_row17_traceSegment_037_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 668 10 10, g32p_row17_traceSegment_037_0668_0010, g32p_row17_traceSegment_037_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 648 20 20, g32p_row17_traceSegment_037_0648_0020, g32p_row17_traceSegment_037_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 688 10 10, g32p_row17_traceSegment_037_0688_0010, g32p_row17_traceSegment_037_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 708 10 11, g32p_row17_traceSegment_037_0708_0010, g32p_row17_traceSegment_037_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 688 20 21, g32p_row17_traceSegment_037_0688_0020, g32p_row17_traceSegment_037_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 648 40 41, g32p_row17_traceSegment_037_0648_0040, g32p_row17_traceSegment_037_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 729 10 10, g32p_row17_traceSegment_037_0729_0010, g32p_row17_traceSegment_037_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 749 10 10, g32p_row17_traceSegment_037_0749_0010, g32p_row17_traceSegment_037_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 729 20 20, g32p_row17_traceSegment_037_0729_0020, g32p_row17_traceSegment_037_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 769 10 10, g32p_row17_traceSegment_037_0769_0010, g32p_row17_traceSegment_037_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 789 10 11, g32p_row17_traceSegment_037_0789_0010, g32p_row17_traceSegment_037_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 769 20 21, g32p_row17_traceSegment_037_0769_0020, g32p_row17_traceSegment_037_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 729 40 41, g32p_row17_traceSegment_037_0729_0040, g32p_row17_traceSegment_037_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_037 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 648 81 81, g32p_row17_traceSegment_037_0648_0081, g32p_row17_traceSegment_037_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 810 10 10, g32p_row17_traceSegment_037_0810_0010, g32p_row17_traceSegment_037_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 830 10 10, g32p_row17_traceSegment_037_0830_0010, g32p_row17_traceSegment_037_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 810 20 20, g32p_row17_traceSegment_037_0810_0020, g32p_row17_traceSegment_037_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 850 10 10, g32p_row17_traceSegment_037_0850_0010, g32p_row17_traceSegment_037_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 870 10 11, g32p_row17_traceSegment_037_0870_0010, g32p_row17_traceSegment_037_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 850 20 21, g32p_row17_traceSegment_037_0850_0020, g32p_row17_traceSegment_037_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 810 40 41, g32p_row17_traceSegment_037_0810_0040, g32p_row17_traceSegment_037_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 891 10 10, g32p_row17_traceSegment_037_0891_0010, g32p_row17_traceSegment_037_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 911 10 10, g32p_row17_traceSegment_037_0911_0010, g32p_row17_traceSegment_037_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 891 20 20, g32p_row17_traceSegment_037_0891_0020, g32p_row17_traceSegment_037_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 931 10 10, g32p_row17_traceSegment_037_0931_0010, g32p_row17_traceSegment_037_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 951 10 11, g32p_row17_traceSegment_037_0951_0010, g32p_row17_traceSegment_037_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 931 20 21, g32p_row17_traceSegment_037_0931_0020, g32p_row17_traceSegment_037_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 891 40 41, g32p_row17_traceSegment_037_0891_0040, g32p_row17_traceSegment_037_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_037 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 810 81 81, g32p_row17_traceSegment_037_0810_0081, g32p_row17_traceSegment_037_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_037 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 648 162 162, g32p_row17_traceSegment_037_0648_0162, g32p_row17_traceSegment_037_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 972 10 10, g32p_row17_traceSegment_037_0972_0010, g32p_row17_traceSegment_037_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 992 10 10, g32p_row17_traceSegment_037_0992_0010, g32p_row17_traceSegment_037_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 972 20 20, g32p_row17_traceSegment_037_0972_0020, g32p_row17_traceSegment_037_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1012 10 10, g32p_row17_traceSegment_037_1012_0010, g32p_row17_traceSegment_037_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1032 10 11, g32p_row17_traceSegment_037_1032_0010, g32p_row17_traceSegment_037_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1012 20 21, g32p_row17_traceSegment_037_1012_0020, g32p_row17_traceSegment_037_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 972 40 41, g32p_row17_traceSegment_037_0972_0040, g32p_row17_traceSegment_037_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1053 10 10, g32p_row17_traceSegment_037_1053_0010, g32p_row17_traceSegment_037_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1073 10 10, g32p_row17_traceSegment_037_1073_0010, g32p_row17_traceSegment_037_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1053 20 20, g32p_row17_traceSegment_037_1053_0020, g32p_row17_traceSegment_037_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1093 10 10, g32p_row17_traceSegment_037_1093_0010, g32p_row17_traceSegment_037_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1113 10 11, g32p_row17_traceSegment_037_1113_0010, g32p_row17_traceSegment_037_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1093 20 21, g32p_row17_traceSegment_037_1093_0020, g32p_row17_traceSegment_037_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1053 40 41, g32p_row17_traceSegment_037_1053_0040, g32p_row17_traceSegment_037_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_037 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 972 81 81, g32p_row17_traceSegment_037_0972_0081, g32p_row17_traceSegment_037_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1134 10 10, g32p_row17_traceSegment_037_1134_0010, g32p_row17_traceSegment_037_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1154 10 10, g32p_row17_traceSegment_037_1154_0010, g32p_row17_traceSegment_037_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1134 20 20, g32p_row17_traceSegment_037_1134_0020, g32p_row17_traceSegment_037_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1174 10 10, g32p_row17_traceSegment_037_1174_0010, g32p_row17_traceSegment_037_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1194 10 11, g32p_row17_traceSegment_037_1194_0010, g32p_row17_traceSegment_037_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1174 20 21, g32p_row17_traceSegment_037_1174_0020, g32p_row17_traceSegment_037_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1134 40 41, g32p_row17_traceSegment_037_1134_0040, g32p_row17_traceSegment_037_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1215 10 10, g32p_row17_traceSegment_037_1215_0010, g32p_row17_traceSegment_037_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1235 10 10, g32p_row17_traceSegment_037_1235_0010, g32p_row17_traceSegment_037_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_037 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1215 20 20, g32p_row17_traceSegment_037_1215_0020, g32p_row17_traceSegment_037_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_037 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1255 10 10, g32p_row17_traceSegment_037_1255_0010, g32p_row17_traceSegment_037_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_037 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_037 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_037_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_037 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1275 10 11, g32p_row17_traceSegment_037_1275_0010, g32p_row17_traceSegment_037_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_037 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1255 20 21, g32p_row17_traceSegment_037_1255_0020, g32p_row17_traceSegment_037_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_037 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1215 40 41, g32p_row17_traceSegment_037_1215_0040, g32p_row17_traceSegment_037_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_037_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_037 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 1134 81 81, g32p_row17_traceSegment_037_1134_0081, g32p_row17_traceSegment_037_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_037 972 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 972 162 162, g32p_row17_traceSegment_037_0972_0162, g32p_row17_traceSegment_037_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_037 648 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 648 324 324, g32p_row17_traceSegment_037_0648_0324, g32p_row17_traceSegment_037_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_037_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_037 0 1296 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_037 0 648 648, g32p_row17_traceSegment_037_0000_0648, g32p_row17_traceSegment_037_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 37 = [0, 0, 0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_037_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_tracePolynomial_025 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 25) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 25) (g32p_literalTraceValue 16 25)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_025]
  decide +kernel

theorem g32p_row17_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 28) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 28) (g32p_literalTraceValue 16 28)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_028]
  decide +kernel

theorem g32p_row17_tracePolynomial_029 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 29) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 29) (g32p_literalTraceValue 16 29)
      [1, -1, 1] [1296, 1296, 1296] = true := by
  rw [g32p_row17_traceCoefficients_029]
  decide +kernel

theorem g32p_row17_tracePolynomial_030 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 30) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 30) (g32p_literalTraceValue 16 30)
      [1, -1, 1] [-1296, 1296, 1296] = true := by
  rw [g32p_row17_traceCoefficients_030]
  decide +kernel

theorem g32p_row17_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 32) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 32) (g32p_literalTraceValue 16 32)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row17_traceCoefficients_032]
  decide +kernel

theorem g32p_row17_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 34) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 34) (g32p_literalTraceValue 16 34)
      [1, -1, 1] [-5184, 5184, 5184] = true := by
  rw [g32p_row17_traceCoefficients_034]
  decide +kernel

theorem g32p_row17_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 35) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 35) (g32p_literalTraceValue 16 35)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row17_traceCoefficients_035]
  decide +kernel

theorem g32p_row17_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 37) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 37) (g32p_literalTraceValue 16 37)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row17_traceCoefficients_037]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
