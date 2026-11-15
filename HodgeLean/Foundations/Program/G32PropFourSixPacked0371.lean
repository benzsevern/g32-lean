import HodgeLean.Foundations.Program.G32PropFourSixPacked0367
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0370

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_056 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 56 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_056_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 0 10 10, g32p_row17_traceSegment_056_0000_0010, g32p_row17_traceSegment_056_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 20 10 10, g32p_row17_traceSegment_056_0020_0010, g32p_row17_traceSegment_056_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 0 20 20, g32p_row17_traceSegment_056_0000_0020, g32p_row17_traceSegment_056_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 40 10 10, g32p_row17_traceSegment_056_0040_0010, g32p_row17_traceSegment_056_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 60 10 11, g32p_row17_traceSegment_056_0060_0010, g32p_row17_traceSegment_056_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 40 20 21, g32p_row17_traceSegment_056_0040_0020, g32p_row17_traceSegment_056_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 0 40 41, g32p_row17_traceSegment_056_0000_0040, g32p_row17_traceSegment_056_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 81 10 10, g32p_row17_traceSegment_056_0081_0010, g32p_row17_traceSegment_056_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 101 10 10, g32p_row17_traceSegment_056_0101_0010, g32p_row17_traceSegment_056_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 81 20 20, g32p_row17_traceSegment_056_0081_0020, g32p_row17_traceSegment_056_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 121 10 10, g32p_row17_traceSegment_056_0121_0010, g32p_row17_traceSegment_056_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 141 10 11, g32p_row17_traceSegment_056_0141_0010, g32p_row17_traceSegment_056_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 121 20 21, g32p_row17_traceSegment_056_0121_0020, g32p_row17_traceSegment_056_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 81 40 41, g32p_row17_traceSegment_056_0081_0040, g32p_row17_traceSegment_056_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_056 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 0 81 81, g32p_row17_traceSegment_056_0000_0081, g32p_row17_traceSegment_056_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 162 10 10, g32p_row17_traceSegment_056_0162_0010, g32p_row17_traceSegment_056_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 182 10 10, g32p_row17_traceSegment_056_0182_0010, g32p_row17_traceSegment_056_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 162 20 20, g32p_row17_traceSegment_056_0162_0020, g32p_row17_traceSegment_056_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 202 10 10, g32p_row17_traceSegment_056_0202_0010, g32p_row17_traceSegment_056_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 222 10 11, g32p_row17_traceSegment_056_0222_0010, g32p_row17_traceSegment_056_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 202 20 21, g32p_row17_traceSegment_056_0202_0020, g32p_row17_traceSegment_056_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 162 40 41, g32p_row17_traceSegment_056_0162_0040, g32p_row17_traceSegment_056_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 243 10 10, g32p_row17_traceSegment_056_0243_0010, g32p_row17_traceSegment_056_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 263 10 10, g32p_row17_traceSegment_056_0263_0010, g32p_row17_traceSegment_056_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 243 20 20, g32p_row17_traceSegment_056_0243_0020, g32p_row17_traceSegment_056_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 283 10 10, g32p_row17_traceSegment_056_0283_0010, g32p_row17_traceSegment_056_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 303 10 11, g32p_row17_traceSegment_056_0303_0010, g32p_row17_traceSegment_056_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 283 20 21, g32p_row17_traceSegment_056_0283_0020, g32p_row17_traceSegment_056_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 243 40 41, g32p_row17_traceSegment_056_0243_0040, g32p_row17_traceSegment_056_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_056 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 162 81 81, g32p_row17_traceSegment_056_0162_0081, g32p_row17_traceSegment_056_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_056 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 0 162 162, g32p_row17_traceSegment_056_0000_0162, g32p_row17_traceSegment_056_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 324 10 10, g32p_row17_traceSegment_056_0324_0010, g32p_row17_traceSegment_056_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 344 10 10, g32p_row17_traceSegment_056_0344_0010, g32p_row17_traceSegment_056_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 324 20 20, g32p_row17_traceSegment_056_0324_0020, g32p_row17_traceSegment_056_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 364 10 10, g32p_row17_traceSegment_056_0364_0010, g32p_row17_traceSegment_056_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 384 10 11, g32p_row17_traceSegment_056_0384_0010, g32p_row17_traceSegment_056_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 364 20 21, g32p_row17_traceSegment_056_0364_0020, g32p_row17_traceSegment_056_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 324 40 41, g32p_row17_traceSegment_056_0324_0040, g32p_row17_traceSegment_056_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 405 10 10, g32p_row17_traceSegment_056_0405_0010, g32p_row17_traceSegment_056_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 425 10 10, g32p_row17_traceSegment_056_0425_0010, g32p_row17_traceSegment_056_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 405 20 20, g32p_row17_traceSegment_056_0405_0020, g32p_row17_traceSegment_056_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 445 10 10, g32p_row17_traceSegment_056_0445_0010, g32p_row17_traceSegment_056_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 465 10 11, g32p_row17_traceSegment_056_0465_0010, g32p_row17_traceSegment_056_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 445 20 21, g32p_row17_traceSegment_056_0445_0020, g32p_row17_traceSegment_056_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 405 40 41, g32p_row17_traceSegment_056_0405_0040, g32p_row17_traceSegment_056_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_056 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 324 81 81, g32p_row17_traceSegment_056_0324_0081, g32p_row17_traceSegment_056_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 486 10 10, g32p_row17_traceSegment_056_0486_0010, g32p_row17_traceSegment_056_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 506 10 10, g32p_row17_traceSegment_056_0506_0010, g32p_row17_traceSegment_056_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 486 20 20, g32p_row17_traceSegment_056_0486_0020, g32p_row17_traceSegment_056_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 526 10 10, g32p_row17_traceSegment_056_0526_0010, g32p_row17_traceSegment_056_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 546 10 11, g32p_row17_traceSegment_056_0546_0010, g32p_row17_traceSegment_056_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 526 20 21, g32p_row17_traceSegment_056_0526_0020, g32p_row17_traceSegment_056_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 486 40 41, g32p_row17_traceSegment_056_0486_0040, g32p_row17_traceSegment_056_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 567 10 10, g32p_row17_traceSegment_056_0567_0010, g32p_row17_traceSegment_056_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 587 10 10, g32p_row17_traceSegment_056_0587_0010, g32p_row17_traceSegment_056_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 567 20 20, g32p_row17_traceSegment_056_0567_0020, g32p_row17_traceSegment_056_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 607 10 10, g32p_row17_traceSegment_056_0607_0010, g32p_row17_traceSegment_056_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 627 10 11, g32p_row17_traceSegment_056_0627_0010, g32p_row17_traceSegment_056_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 607 20 21, g32p_row17_traceSegment_056_0607_0020, g32p_row17_traceSegment_056_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 567 40 41, g32p_row17_traceSegment_056_0567_0040, g32p_row17_traceSegment_056_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_056 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 486 81 81, g32p_row17_traceSegment_056_0486_0081, g32p_row17_traceSegment_056_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_056 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 324 162 162, g32p_row17_traceSegment_056_0324_0162, g32p_row17_traceSegment_056_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_056 0 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 0 324 324, g32p_row17_traceSegment_056_0000_0324, g32p_row17_traceSegment_056_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 648 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 648 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 648 10 10, g32p_row17_traceSegment_056_0648_0010, g32p_row17_traceSegment_056_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 668 10 10, g32p_row17_traceSegment_056_0668_0010, g32p_row17_traceSegment_056_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 648 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 648 20 20, g32p_row17_traceSegment_056_0648_0020, g32p_row17_traceSegment_056_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 688 10 10, g32p_row17_traceSegment_056_0688_0010, g32p_row17_traceSegment_056_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 708 10 11, g32p_row17_traceSegment_056_0708_0010, g32p_row17_traceSegment_056_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 688 20 21, g32p_row17_traceSegment_056_0688_0020, g32p_row17_traceSegment_056_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 648 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 648 40 41, g32p_row17_traceSegment_056_0648_0040, g32p_row17_traceSegment_056_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 729 10 10, g32p_row17_traceSegment_056_0729_0010, g32p_row17_traceSegment_056_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 749 10 10, g32p_row17_traceSegment_056_0749_0010, g32p_row17_traceSegment_056_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 729 20 20, g32p_row17_traceSegment_056_0729_0020, g32p_row17_traceSegment_056_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 769 10 10, g32p_row17_traceSegment_056_0769_0010, g32p_row17_traceSegment_056_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 789 10 11, g32p_row17_traceSegment_056_0789_0010, g32p_row17_traceSegment_056_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 769 20 21, g32p_row17_traceSegment_056_0769_0020, g32p_row17_traceSegment_056_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 729 40 41, g32p_row17_traceSegment_056_0729_0040, g32p_row17_traceSegment_056_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_056 648 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 648 81 81, g32p_row17_traceSegment_056_0648_0081, g32p_row17_traceSegment_056_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 810 10 10, g32p_row17_traceSegment_056_0810_0010, g32p_row17_traceSegment_056_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 840 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 830 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 830 10 10, g32p_row17_traceSegment_056_0830_0010, g32p_row17_traceSegment_056_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 810 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 810 20 20, g32p_row17_traceSegment_056_0810_0020, g32p_row17_traceSegment_056_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 850 10 10, g32p_row17_traceSegment_056_0850_0010, g32p_row17_traceSegment_056_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 870 10 11, g32p_row17_traceSegment_056_0870_0010, g32p_row17_traceSegment_056_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 850 20 21, g32p_row17_traceSegment_056_0850_0020, g32p_row17_traceSegment_056_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 810 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 810 40 41, g32p_row17_traceSegment_056_0810_0040, g32p_row17_traceSegment_056_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 891 10 10, g32p_row17_traceSegment_056_0891_0010, g32p_row17_traceSegment_056_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 911 10 10, g32p_row17_traceSegment_056_0911_0010, g32p_row17_traceSegment_056_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 891 20 20, g32p_row17_traceSegment_056_0891_0020, g32p_row17_traceSegment_056_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 931 10 10, g32p_row17_traceSegment_056_0931_0010, g32p_row17_traceSegment_056_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 951 10 11, g32p_row17_traceSegment_056_0951_0010, g32p_row17_traceSegment_056_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 931 20 21, g32p_row17_traceSegment_056_0931_0020, g32p_row17_traceSegment_056_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 891 40 41, g32p_row17_traceSegment_056_0891_0040, g32p_row17_traceSegment_056_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_056 810 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 810 81 81, g32p_row17_traceSegment_056_0810_0081, g32p_row17_traceSegment_056_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_056 648 324 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 648 162 162, g32p_row17_traceSegment_056_0648_0162, g32p_row17_traceSegment_056_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 972 10 10, g32p_row17_traceSegment_056_0972_0010, g32p_row17_traceSegment_056_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 992 10 10, g32p_row17_traceSegment_056_0992_0010, g32p_row17_traceSegment_056_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 972 20 20, g32p_row17_traceSegment_056_0972_0020, g32p_row17_traceSegment_056_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1012 10 10, g32p_row17_traceSegment_056_1012_0010, g32p_row17_traceSegment_056_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1032 10 11, g32p_row17_traceSegment_056_1032_0010, g32p_row17_traceSegment_056_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1012 20 21, g32p_row17_traceSegment_056_1012_0020, g32p_row17_traceSegment_056_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 972 40 41, g32p_row17_traceSegment_056_0972_0040, g32p_row17_traceSegment_056_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1053 10 10, g32p_row17_traceSegment_056_1053_0010, g32p_row17_traceSegment_056_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1073 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 1073 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1073 10 10, g32p_row17_traceSegment_056_1073_0010, g32p_row17_traceSegment_056_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 1053 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1053 20 20, g32p_row17_traceSegment_056_1053_0020, g32p_row17_traceSegment_056_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1093 10 10, g32p_row17_traceSegment_056_1093_0010, g32p_row17_traceSegment_056_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1113 10 11, g32p_row17_traceSegment_056_1113_0010, g32p_row17_traceSegment_056_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1093 20 21, g32p_row17_traceSegment_056_1093_0020, g32p_row17_traceSegment_056_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 1053 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1053 40 41, g32p_row17_traceSegment_056_1053_0040, g32p_row17_traceSegment_056_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_056 972 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 972 81 81, g32p_row17_traceSegment_056_0972_0081, g32p_row17_traceSegment_056_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1134 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 1134 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1134 10 10, g32p_row17_traceSegment_056_1134_0010, g32p_row17_traceSegment_056_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1154 10 10, g32p_row17_traceSegment_056_1154_0010, g32p_row17_traceSegment_056_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 1134 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1134 20 20, g32p_row17_traceSegment_056_1134_0020, g32p_row17_traceSegment_056_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1174 10 10, g32p_row17_traceSegment_056_1174_0010, g32p_row17_traceSegment_056_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1194 10 11, g32p_row17_traceSegment_056_1194_0010, g32p_row17_traceSegment_056_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1174 20 21, g32p_row17_traceSegment_056_1174_0020, g32p_row17_traceSegment_056_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 1134 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1134 40 41, g32p_row17_traceSegment_056_1134_0040, g32p_row17_traceSegment_056_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1215 10 10, g32p_row17_traceSegment_056_1215_0010, g32p_row17_traceSegment_056_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1235 10 10, g32p_row17_traceSegment_056_1235_0010, g32p_row17_traceSegment_056_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_056 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1215 20 20, g32p_row17_traceSegment_056_1215_0020, g32p_row17_traceSegment_056_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1265 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_056 1255 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1255 10 10, g32p_row17_traceSegment_056_1255_0010, g32p_row17_traceSegment_056_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_056 1275 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_056 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_056_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_056 1275 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1275 10 11, g32p_row17_traceSegment_056_1275_0010, g32p_row17_traceSegment_056_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_056 1255 41 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1255 20 21, g32p_row17_traceSegment_056_1255_0020, g32p_row17_traceSegment_056_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_056 1215 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1215 40 41, g32p_row17_traceSegment_056_1215_0040, g32p_row17_traceSegment_056_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_056_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_056 1134 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 1134 81 81, g32p_row17_traceSegment_056_1134_0081, g32p_row17_traceSegment_056_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_056 972 324 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 972 162 162, g32p_row17_traceSegment_056_0972_0162, g32p_row17_traceSegment_056_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_056 648 648 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 648 324 324, g32p_row17_traceSegment_056_0648_0324, g32p_row17_traceSegment_056_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_056_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_056 0 1296 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_056 0 648 648, g32p_row17_traceSegment_056_0000_0648, g32p_row17_traceSegment_056_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 56 = [0, 0, 6] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_056_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_057 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 57 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_057_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 0 10 10, g32p_row17_traceSegment_057_0000_0010, g32p_row17_traceSegment_057_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 30 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 20 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 20 10 10, g32p_row17_traceSegment_057_0020_0010, g32p_row17_traceSegment_057_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 0 40 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 0 20 20, g32p_row17_traceSegment_057_0000_0020, g32p_row17_traceSegment_057_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 40 10 10, g32p_row17_traceSegment_057_0040_0010, g32p_row17_traceSegment_057_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 60 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 60 21 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 60 10 11, g32p_row17_traceSegment_057_0060_0010, g32p_row17_traceSegment_057_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 40 41 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 40 20 21, g32p_row17_traceSegment_057_0040_0020, g32p_row17_traceSegment_057_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 0 81 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 0 40 41, g32p_row17_traceSegment_057_0000_0040, g32p_row17_traceSegment_057_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 81 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 81 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 81 10 10, g32p_row17_traceSegment_057_0081_0010, g32p_row17_traceSegment_057_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 101 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 111 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 101 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 101 10 10, g32p_row17_traceSegment_057_0101_0010, g32p_row17_traceSegment_057_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 81 40 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 81 20 20, g32p_row17_traceSegment_057_0081_0020, g32p_row17_traceSegment_057_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 121 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 131 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 121 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 121 10 10, g32p_row17_traceSegment_057_0121_0010, g32p_row17_traceSegment_057_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 141 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 141 21 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 141 10 11, g32p_row17_traceSegment_057_0141_0010, g32p_row17_traceSegment_057_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 121 41 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 121 20 21, g32p_row17_traceSegment_057_0121_0020, g32p_row17_traceSegment_057_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 81 81 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 81 40 41, g32p_row17_traceSegment_057_0081_0040, g32p_row17_traceSegment_057_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_057 0 162 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 0 81 81, g32p_row17_traceSegment_057_0000_0081, g32p_row17_traceSegment_057_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 162 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 162 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 162 10 10, g32p_row17_traceSegment_057_0162_0010, g32p_row17_traceSegment_057_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 182 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 192 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 182 20 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 182 10 10, g32p_row17_traceSegment_057_0182_0010, g32p_row17_traceSegment_057_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 162 40 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 162 20 20, g32p_row17_traceSegment_057_0162_0020, g32p_row17_traceSegment_057_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 202 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 202 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 202 10 10, g32p_row17_traceSegment_057_0202_0010, g32p_row17_traceSegment_057_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 232 11 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 222 21 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 222 10 11, g32p_row17_traceSegment_057_0222_0010, g32p_row17_traceSegment_057_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 202 41 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 202 20 21, g32p_row17_traceSegment_057_0202_0020, g32p_row17_traceSegment_057_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 162 81 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 162 40 41, g32p_row17_traceSegment_057_0162_0040, g32p_row17_traceSegment_057_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 253 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 243 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 243 10 10, g32p_row17_traceSegment_057_0243_0010, g32p_row17_traceSegment_057_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 263 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 263 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 263 10 10, g32p_row17_traceSegment_057_0263_0010, g32p_row17_traceSegment_057_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 243 40 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 243 20 20, g32p_row17_traceSegment_057_0243_0020, g32p_row17_traceSegment_057_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 283 10 10, g32p_row17_traceSegment_057_0283_0010, g32p_row17_traceSegment_057_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 303 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 313 11 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 303 21 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 303 10 11, g32p_row17_traceSegment_057_0303_0010, g32p_row17_traceSegment_057_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 283 41 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 283 20 21, g32p_row17_traceSegment_057_0283_0020, g32p_row17_traceSegment_057_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 243 81 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 243 40 41, g32p_row17_traceSegment_057_0243_0040, g32p_row17_traceSegment_057_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_057 162 162 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 162 81 81, g32p_row17_traceSegment_057_0162_0081, g32p_row17_traceSegment_057_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_057 0 324 = [0, 22] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 0 162 162, g32p_row17_traceSegment_057_0000_0162, g32p_row17_traceSegment_057_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 324 10 10, g32p_row17_traceSegment_057_0324_0010, g32p_row17_traceSegment_057_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 344 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 354 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 344 20 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 344 10 10, g32p_row17_traceSegment_057_0344_0010, g32p_row17_traceSegment_057_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 324 40 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 324 20 20, g32p_row17_traceSegment_057_0324_0020, g32p_row17_traceSegment_057_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 364 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 374 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 364 20 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 364 10 10, g32p_row17_traceSegment_057_0364_0010, g32p_row17_traceSegment_057_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 384 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 394 11 = [0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 384 21 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 384 10 11, g32p_row17_traceSegment_057_0384_0010, g32p_row17_traceSegment_057_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 364 41 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 364 20 21, g32p_row17_traceSegment_057_0364_0020, g32p_row17_traceSegment_057_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 324 81 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 324 40 41, g32p_row17_traceSegment_057_0324_0040, g32p_row17_traceSegment_057_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 405 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 405 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 405 10 10, g32p_row17_traceSegment_057_0405_0010, g32p_row17_traceSegment_057_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 435 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 425 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 425 10 10, g32p_row17_traceSegment_057_0425_0010, g32p_row17_traceSegment_057_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 405 40 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 405 20 20, g32p_row17_traceSegment_057_0405_0020, g32p_row17_traceSegment_057_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 445 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 455 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 445 20 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 445 10 10, g32p_row17_traceSegment_057_0445_0010, g32p_row17_traceSegment_057_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 475 11 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 465 21 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 465 10 11, g32p_row17_traceSegment_057_0465_0010, g32p_row17_traceSegment_057_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 445 41 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 445 20 21, g32p_row17_traceSegment_057_0445_0020, g32p_row17_traceSegment_057_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 405 81 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 405 40 41, g32p_row17_traceSegment_057_0405_0040, g32p_row17_traceSegment_057_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_057 324 162 = [0, 17] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 324 81 81, g32p_row17_traceSegment_057_0324_0081, g32p_row17_traceSegment_057_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 486 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 496 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 486 20 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 486 10 10, g32p_row17_traceSegment_057_0486_0010, g32p_row17_traceSegment_057_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 516 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 506 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 506 10 10, g32p_row17_traceSegment_057_0506_0010, g32p_row17_traceSegment_057_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 486 40 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 486 20 20, g32p_row17_traceSegment_057_0486_0020, g32p_row17_traceSegment_057_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 526 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 536 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 526 20 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 526 10 10, g32p_row17_traceSegment_057_0526_0010, g32p_row17_traceSegment_057_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 556 11 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 546 21 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 546 10 11, g32p_row17_traceSegment_057_0546_0010, g32p_row17_traceSegment_057_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 526 41 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 526 20 21, g32p_row17_traceSegment_057_0526_0020, g32p_row17_traceSegment_057_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 486 81 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 486 40 41, g32p_row17_traceSegment_057_0486_0040, g32p_row17_traceSegment_057_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 567 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 577 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 567 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 567 10 10, g32p_row17_traceSegment_057_0567_0010, g32p_row17_traceSegment_057_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 597 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 587 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 587 10 10, g32p_row17_traceSegment_057_0587_0010, g32p_row17_traceSegment_057_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 567 40 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 567 20 20, g32p_row17_traceSegment_057_0567_0020, g32p_row17_traceSegment_057_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 607 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 617 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 607 20 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 607 10 10, g32p_row17_traceSegment_057_0607_0010, g32p_row17_traceSegment_057_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 637 11 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 627 21 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 627 10 11, g32p_row17_traceSegment_057_0627_0010, g32p_row17_traceSegment_057_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 607 41 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 607 20 21, g32p_row17_traceSegment_057_0607_0020, g32p_row17_traceSegment_057_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 567 81 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 567 40 41, g32p_row17_traceSegment_057_0567_0040, g32p_row17_traceSegment_057_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_057 486 162 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 486 81 81, g32p_row17_traceSegment_057_0486_0081, g32p_row17_traceSegment_057_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_057 324 324 = [0, 35] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 324 162 162, g32p_row17_traceSegment_057_0324_0162, g32p_row17_traceSegment_057_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_057 0 648 = [0, 57] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 0 324 324, g32p_row17_traceSegment_057_0000_0324, g32p_row17_traceSegment_057_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 658 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 648 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 648 10 10, g32p_row17_traceSegment_057_0648_0010, g32p_row17_traceSegment_057_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 668 10 10, g32p_row17_traceSegment_057_0668_0010, g32p_row17_traceSegment_057_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 648 40 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 648 20 20, g32p_row17_traceSegment_057_0648_0020, g32p_row17_traceSegment_057_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 698 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 688 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 688 10 10, g32p_row17_traceSegment_057_0688_0010, g32p_row17_traceSegment_057_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 708 10 11, g32p_row17_traceSegment_057_0708_0010, g32p_row17_traceSegment_057_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 688 41 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 688 20 21, g32p_row17_traceSegment_057_0688_0020, g32p_row17_traceSegment_057_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 648 81 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 648 40 41, g32p_row17_traceSegment_057_0648_0040, g32p_row17_traceSegment_057_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 739 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 729 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 729 10 10, g32p_row17_traceSegment_057_0729_0010, g32p_row17_traceSegment_057_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 749 10 10, g32p_row17_traceSegment_057_0749_0010, g32p_row17_traceSegment_057_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 729 40 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 729 20 20, g32p_row17_traceSegment_057_0729_0020, g32p_row17_traceSegment_057_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 769 10 10, g32p_row17_traceSegment_057_0769_0010, g32p_row17_traceSegment_057_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 789 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 789 21 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 789 10 11, g32p_row17_traceSegment_057_0789_0010, g32p_row17_traceSegment_057_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 769 41 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 769 20 21, g32p_row17_traceSegment_057_0769_0020, g32p_row17_traceSegment_057_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 729 81 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 729 40 41, g32p_row17_traceSegment_057_0729_0040, g32p_row17_traceSegment_057_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_057 648 162 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 648 81 81, g32p_row17_traceSegment_057_0648_0081, g32p_row17_traceSegment_057_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 810 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 820 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 810 20 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 810 10 10, g32p_row17_traceSegment_057_0810_0010, g32p_row17_traceSegment_057_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 830 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 830 20 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 830 10 10, g32p_row17_traceSegment_057_0830_0010, g32p_row17_traceSegment_057_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 810 40 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 810 20 20, g32p_row17_traceSegment_057_0810_0020, g32p_row17_traceSegment_057_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 850 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 860 10 = [0, 4] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 850 20 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 850 10 10, g32p_row17_traceSegment_057_0850_0010, g32p_row17_traceSegment_057_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 880 11 = [0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 870 21 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 870 10 11, g32p_row17_traceSegment_057_0870_0010, g32p_row17_traceSegment_057_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 850 41 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 850 20 21, g32p_row17_traceSegment_057_0850_0020, g32p_row17_traceSegment_057_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 810 81 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 810 40 41, g32p_row17_traceSegment_057_0810_0040, g32p_row17_traceSegment_057_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 891 10 10, g32p_row17_traceSegment_057_0891_0010, g32p_row17_traceSegment_057_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 921 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 911 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 911 10 10, g32p_row17_traceSegment_057_0911_0010, g32p_row17_traceSegment_057_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 891 40 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 891 20 20, g32p_row17_traceSegment_057_0891_0020, g32p_row17_traceSegment_057_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 941 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 931 20 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 931 10 10, g32p_row17_traceSegment_057_0931_0010, g32p_row17_traceSegment_057_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 961 11 = [0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 951 21 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 951 10 11, g32p_row17_traceSegment_057_0951_0010, g32p_row17_traceSegment_057_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 931 41 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 931 20 21, g32p_row17_traceSegment_057_0931_0020, g32p_row17_traceSegment_057_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 891 81 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 891 40 41, g32p_row17_traceSegment_057_0891_0040, g32p_row17_traceSegment_057_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_057 810 162 = [0, 22] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 810 81 81, g32p_row17_traceSegment_057_0810_0081, g32p_row17_traceSegment_057_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_057 648 324 = [0, 27] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 648 162 162, g32p_row17_traceSegment_057_0648_0162, g32p_row17_traceSegment_057_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 972 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 972 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 972 10 10, g32p_row17_traceSegment_057_0972_0010, g32p_row17_traceSegment_057_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 992 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1002 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 992 20 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 992 10 10, g32p_row17_traceSegment_057_0992_0010, g32p_row17_traceSegment_057_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 972 40 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 972 20 20, g32p_row17_traceSegment_057_0972_0020, g32p_row17_traceSegment_057_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1012 10 10, g32p_row17_traceSegment_057_1012_0010, g32p_row17_traceSegment_057_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1032 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 1042 11 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 1032 21 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1032 10 11, g32p_row17_traceSegment_057_1032_0010, g32p_row17_traceSegment_057_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 1012 41 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1012 20 21, g32p_row17_traceSegment_057_1012_0020, g32p_row17_traceSegment_057_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 972 81 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 972 40 41, g32p_row17_traceSegment_057_0972_0040, g32p_row17_traceSegment_057_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1053 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 1053 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1053 10 10, g32p_row17_traceSegment_057_1053_0010, g32p_row17_traceSegment_057_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1083 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 1073 20 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1073 10 10, g32p_row17_traceSegment_057_1073_0010, g32p_row17_traceSegment_057_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 1053 40 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1053 20 20, g32p_row17_traceSegment_057_1053_0020, g32p_row17_traceSegment_057_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1093 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 1093 20 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1093 10 10, g32p_row17_traceSegment_057_1093_0010, g32p_row17_traceSegment_057_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1113 10 11, g32p_row17_traceSegment_057_1113_0010, g32p_row17_traceSegment_057_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 1093 41 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1093 20 21, g32p_row17_traceSegment_057_1093_0020, g32p_row17_traceSegment_057_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 1053 81 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1053 40 41, g32p_row17_traceSegment_057_1053_0040, g32p_row17_traceSegment_057_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_057 972 162 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 972 81 81, g32p_row17_traceSegment_057_0972_0081, g32p_row17_traceSegment_057_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1134 10 10, g32p_row17_traceSegment_057_1134_0010, g32p_row17_traceSegment_057_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1154 10 10, g32p_row17_traceSegment_057_1154_0010, g32p_row17_traceSegment_057_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1134 20 20, g32p_row17_traceSegment_057_1134_0020, g32p_row17_traceSegment_057_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1174 10 10, g32p_row17_traceSegment_057_1174_0010, g32p_row17_traceSegment_057_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1194 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 1194 21 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1194 10 11, g32p_row17_traceSegment_057_1194_0010, g32p_row17_traceSegment_057_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 1174 41 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1174 20 21, g32p_row17_traceSegment_057_1174_0020, g32p_row17_traceSegment_057_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 1134 81 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1134 40 41, g32p_row17_traceSegment_057_1134_0040, g32p_row17_traceSegment_057_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1215 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 1215 20 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1215 10 10, g32p_row17_traceSegment_057_1215_0010, g32p_row17_traceSegment_057_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1235 10 = [0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 1235 20 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1235 10 10, g32p_row17_traceSegment_057_1235_0010, g32p_row17_traceSegment_057_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_057 1215 40 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1215 20 20, g32p_row17_traceSegment_057_1215_0020, g32p_row17_traceSegment_057_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1255 10 = [0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1265 10 = [0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_057 1255 20 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1255 10 10, g32p_row17_traceSegment_057_1255_0010, g32p_row17_traceSegment_057_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_057 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_057 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_057_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_057 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1275 10 11, g32p_row17_traceSegment_057_1275_0010, g32p_row17_traceSegment_057_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_057 1255 41 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1255 20 21, g32p_row17_traceSegment_057_1255_0020, g32p_row17_traceSegment_057_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_057 1215 81 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1215 40 41, g32p_row17_traceSegment_057_1215_0040, g32p_row17_traceSegment_057_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_057_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_057 1134 162 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 1134 81 81, g32p_row17_traceSegment_057_1134_0081, g32p_row17_traceSegment_057_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_057 972 324 = [0, 24] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 972 162 162, g32p_row17_traceSegment_057_0972_0162, g32p_row17_traceSegment_057_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_057 648 648 = [0, 51] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 648 324 324, g32p_row17_traceSegment_057_0648_0324, g32p_row17_traceSegment_057_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_057_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_057 0 1296 = [0, 108] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_057 0 648 648, g32p_row17_traceSegment_057_0000_0648, g32p_row17_traceSegment_057_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_057 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 57 = [0, 108] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_057_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_059 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 59 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_059_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 0 10 10, g32p_row17_traceSegment_059_0000_0010, g32p_row17_traceSegment_059_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 20 10 10, g32p_row17_traceSegment_059_0020_0010, g32p_row17_traceSegment_059_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 0 20 20, g32p_row17_traceSegment_059_0000_0020, g32p_row17_traceSegment_059_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 40 10 10, g32p_row17_traceSegment_059_0040_0010, g32p_row17_traceSegment_059_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 60 10 11, g32p_row17_traceSegment_059_0060_0010, g32p_row17_traceSegment_059_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 40 20 21, g32p_row17_traceSegment_059_0040_0020, g32p_row17_traceSegment_059_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 0 40 41, g32p_row17_traceSegment_059_0000_0040, g32p_row17_traceSegment_059_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 81 10 10, g32p_row17_traceSegment_059_0081_0010, g32p_row17_traceSegment_059_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 101 10 10, g32p_row17_traceSegment_059_0101_0010, g32p_row17_traceSegment_059_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 81 20 20, g32p_row17_traceSegment_059_0081_0020, g32p_row17_traceSegment_059_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 121 10 10, g32p_row17_traceSegment_059_0121_0010, g32p_row17_traceSegment_059_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 141 10 11, g32p_row17_traceSegment_059_0141_0010, g32p_row17_traceSegment_059_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 121 20 21, g32p_row17_traceSegment_059_0121_0020, g32p_row17_traceSegment_059_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 81 40 41, g32p_row17_traceSegment_059_0081_0040, g32p_row17_traceSegment_059_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_059 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 0 81 81, g32p_row17_traceSegment_059_0000_0081, g32p_row17_traceSegment_059_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 162 10 10, g32p_row17_traceSegment_059_0162_0010, g32p_row17_traceSegment_059_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 182 10 10, g32p_row17_traceSegment_059_0182_0010, g32p_row17_traceSegment_059_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 162 20 20, g32p_row17_traceSegment_059_0162_0020, g32p_row17_traceSegment_059_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 202 10 10, g32p_row17_traceSegment_059_0202_0010, g32p_row17_traceSegment_059_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 222 10 11, g32p_row17_traceSegment_059_0222_0010, g32p_row17_traceSegment_059_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 202 20 21, g32p_row17_traceSegment_059_0202_0020, g32p_row17_traceSegment_059_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 162 40 41, g32p_row17_traceSegment_059_0162_0040, g32p_row17_traceSegment_059_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 243 10 10, g32p_row17_traceSegment_059_0243_0010, g32p_row17_traceSegment_059_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 263 10 10, g32p_row17_traceSegment_059_0263_0010, g32p_row17_traceSegment_059_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 243 20 20, g32p_row17_traceSegment_059_0243_0020, g32p_row17_traceSegment_059_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 283 10 10, g32p_row17_traceSegment_059_0283_0010, g32p_row17_traceSegment_059_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 303 10 11, g32p_row17_traceSegment_059_0303_0010, g32p_row17_traceSegment_059_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 283 20 21, g32p_row17_traceSegment_059_0283_0020, g32p_row17_traceSegment_059_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 243 40 41, g32p_row17_traceSegment_059_0243_0040, g32p_row17_traceSegment_059_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_059 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 162 81 81, g32p_row17_traceSegment_059_0162_0081, g32p_row17_traceSegment_059_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_059 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 0 162 162, g32p_row17_traceSegment_059_0000_0162, g32p_row17_traceSegment_059_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 324 10 10, g32p_row17_traceSegment_059_0324_0010, g32p_row17_traceSegment_059_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 344 10 10, g32p_row17_traceSegment_059_0344_0010, g32p_row17_traceSegment_059_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 324 20 20, g32p_row17_traceSegment_059_0324_0020, g32p_row17_traceSegment_059_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 364 10 10, g32p_row17_traceSegment_059_0364_0010, g32p_row17_traceSegment_059_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 384 10 11, g32p_row17_traceSegment_059_0384_0010, g32p_row17_traceSegment_059_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 364 20 21, g32p_row17_traceSegment_059_0364_0020, g32p_row17_traceSegment_059_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 324 40 41, g32p_row17_traceSegment_059_0324_0040, g32p_row17_traceSegment_059_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 405 10 10, g32p_row17_traceSegment_059_0405_0010, g32p_row17_traceSegment_059_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 425 10 10, g32p_row17_traceSegment_059_0425_0010, g32p_row17_traceSegment_059_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 405 20 20, g32p_row17_traceSegment_059_0405_0020, g32p_row17_traceSegment_059_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 445 10 10, g32p_row17_traceSegment_059_0445_0010, g32p_row17_traceSegment_059_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 465 10 11, g32p_row17_traceSegment_059_0465_0010, g32p_row17_traceSegment_059_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 445 20 21, g32p_row17_traceSegment_059_0445_0020, g32p_row17_traceSegment_059_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 405 40 41, g32p_row17_traceSegment_059_0405_0040, g32p_row17_traceSegment_059_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_059 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 324 81 81, g32p_row17_traceSegment_059_0324_0081, g32p_row17_traceSegment_059_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 486 10 10, g32p_row17_traceSegment_059_0486_0010, g32p_row17_traceSegment_059_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 506 10 10, g32p_row17_traceSegment_059_0506_0010, g32p_row17_traceSegment_059_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 486 20 20, g32p_row17_traceSegment_059_0486_0020, g32p_row17_traceSegment_059_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 526 10 10, g32p_row17_traceSegment_059_0526_0010, g32p_row17_traceSegment_059_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 546 10 11, g32p_row17_traceSegment_059_0546_0010, g32p_row17_traceSegment_059_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 526 20 21, g32p_row17_traceSegment_059_0526_0020, g32p_row17_traceSegment_059_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 486 40 41, g32p_row17_traceSegment_059_0486_0040, g32p_row17_traceSegment_059_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 567 10 10, g32p_row17_traceSegment_059_0567_0010, g32p_row17_traceSegment_059_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 587 10 10, g32p_row17_traceSegment_059_0587_0010, g32p_row17_traceSegment_059_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 567 20 20, g32p_row17_traceSegment_059_0567_0020, g32p_row17_traceSegment_059_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 607 10 10, g32p_row17_traceSegment_059_0607_0010, g32p_row17_traceSegment_059_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 627 10 11, g32p_row17_traceSegment_059_0627_0010, g32p_row17_traceSegment_059_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 607 20 21, g32p_row17_traceSegment_059_0607_0020, g32p_row17_traceSegment_059_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 567 40 41, g32p_row17_traceSegment_059_0567_0040, g32p_row17_traceSegment_059_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_059 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 486 81 81, g32p_row17_traceSegment_059_0486_0081, g32p_row17_traceSegment_059_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_059 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 324 162 162, g32p_row17_traceSegment_059_0324_0162, g32p_row17_traceSegment_059_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_059 0 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 0 324 324, g32p_row17_traceSegment_059_0000_0324, g32p_row17_traceSegment_059_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 658 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 648 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 648 10 10, g32p_row17_traceSegment_059_0648_0010, g32p_row17_traceSegment_059_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 668 10 10, g32p_row17_traceSegment_059_0668_0010, g32p_row17_traceSegment_059_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 648 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 648 20 20, g32p_row17_traceSegment_059_0648_0020, g32p_row17_traceSegment_059_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 688 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 688 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 688 10 10, g32p_row17_traceSegment_059_0688_0010, g32p_row17_traceSegment_059_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 708 10 11, g32p_row17_traceSegment_059_0708_0010, g32p_row17_traceSegment_059_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 688 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 688 20 21, g32p_row17_traceSegment_059_0688_0020, g32p_row17_traceSegment_059_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 648 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 648 40 41, g32p_row17_traceSegment_059_0648_0040, g32p_row17_traceSegment_059_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 729 10 10, g32p_row17_traceSegment_059_0729_0010, g32p_row17_traceSegment_059_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 749 10 10, g32p_row17_traceSegment_059_0749_0010, g32p_row17_traceSegment_059_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 729 20 20, g32p_row17_traceSegment_059_0729_0020, g32p_row17_traceSegment_059_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 769 10 10, g32p_row17_traceSegment_059_0769_0010, g32p_row17_traceSegment_059_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 789 10 11, g32p_row17_traceSegment_059_0789_0010, g32p_row17_traceSegment_059_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 769 20 21, g32p_row17_traceSegment_059_0769_0020, g32p_row17_traceSegment_059_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 729 40 41, g32p_row17_traceSegment_059_0729_0040, g32p_row17_traceSegment_059_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_059 648 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 648 81 81, g32p_row17_traceSegment_059_0648_0081, g32p_row17_traceSegment_059_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 810 10 10, g32p_row17_traceSegment_059_0810_0010, g32p_row17_traceSegment_059_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 830 10 10, g32p_row17_traceSegment_059_0830_0010, g32p_row17_traceSegment_059_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 810 20 20, g32p_row17_traceSegment_059_0810_0020, g32p_row17_traceSegment_059_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 850 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 850 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 850 10 10, g32p_row17_traceSegment_059_0850_0010, g32p_row17_traceSegment_059_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 870 10 11, g32p_row17_traceSegment_059_0870_0010, g32p_row17_traceSegment_059_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 850 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 850 20 21, g32p_row17_traceSegment_059_0850_0020, g32p_row17_traceSegment_059_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 810 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 810 40 41, g32p_row17_traceSegment_059_0810_0040, g32p_row17_traceSegment_059_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 891 10 10, g32p_row17_traceSegment_059_0891_0010, g32p_row17_traceSegment_059_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 911 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 911 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 911 10 10, g32p_row17_traceSegment_059_0911_0010, g32p_row17_traceSegment_059_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 891 40 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 891 20 20, g32p_row17_traceSegment_059_0891_0020, g32p_row17_traceSegment_059_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 931 10 10, g32p_row17_traceSegment_059_0931_0010, g32p_row17_traceSegment_059_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 951 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 951 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 951 10 11, g32p_row17_traceSegment_059_0951_0010, g32p_row17_traceSegment_059_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 931 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 931 20 21, g32p_row17_traceSegment_059_0931_0020, g32p_row17_traceSegment_059_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 891 81 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 891 40 41, g32p_row17_traceSegment_059_0891_0040, g32p_row17_traceSegment_059_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_059 810 162 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 810 81 81, g32p_row17_traceSegment_059_0810_0081, g32p_row17_traceSegment_059_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_059 648 324 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 648 162 162, g32p_row17_traceSegment_059_0648_0162, g32p_row17_traceSegment_059_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 972 10 10, g32p_row17_traceSegment_059_0972_0010, g32p_row17_traceSegment_059_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 992 10 10, g32p_row17_traceSegment_059_0992_0010, g32p_row17_traceSegment_059_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 972 20 20, g32p_row17_traceSegment_059_0972_0020, g32p_row17_traceSegment_059_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1012 10 10, g32p_row17_traceSegment_059_1012_0010, g32p_row17_traceSegment_059_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1032 10 11, g32p_row17_traceSegment_059_1032_0010, g32p_row17_traceSegment_059_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1012 20 21, g32p_row17_traceSegment_059_1012_0020, g32p_row17_traceSegment_059_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 972 40 41, g32p_row17_traceSegment_059_0972_0040, g32p_row17_traceSegment_059_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1063 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 1053 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1053 10 10, g32p_row17_traceSegment_059_1053_0010, g32p_row17_traceSegment_059_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1073 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 1073 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1073 10 10, g32p_row17_traceSegment_059_1073_0010, g32p_row17_traceSegment_059_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 1053 40 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1053 20 20, g32p_row17_traceSegment_059_1053_0020, g32p_row17_traceSegment_059_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1093 10 10, g32p_row17_traceSegment_059_1093_0010, g32p_row17_traceSegment_059_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1113 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 1113 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1113 10 11, g32p_row17_traceSegment_059_1113_0010, g32p_row17_traceSegment_059_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 1093 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1093 20 21, g32p_row17_traceSegment_059_1093_0020, g32p_row17_traceSegment_059_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 1053 81 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1053 40 41, g32p_row17_traceSegment_059_1053_0040, g32p_row17_traceSegment_059_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_059 972 162 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 972 81 81, g32p_row17_traceSegment_059_0972_0081, g32p_row17_traceSegment_059_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1134 10 10, g32p_row17_traceSegment_059_1134_0010, g32p_row17_traceSegment_059_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1164 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 1154 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1154 10 10, g32p_row17_traceSegment_059_1154_0010, g32p_row17_traceSegment_059_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 1134 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1134 20 20, g32p_row17_traceSegment_059_1134_0020, g32p_row17_traceSegment_059_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1174 10 10, g32p_row17_traceSegment_059_1174_0010, g32p_row17_traceSegment_059_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1194 10 11, g32p_row17_traceSegment_059_1194_0010, g32p_row17_traceSegment_059_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1174 20 21, g32p_row17_traceSegment_059_1174_0020, g32p_row17_traceSegment_059_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 1134 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1134 40 41, g32p_row17_traceSegment_059_1134_0040, g32p_row17_traceSegment_059_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1215 10 10, g32p_row17_traceSegment_059_1215_0010, g32p_row17_traceSegment_059_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1235 10 10, g32p_row17_traceSegment_059_1235_0010, g32p_row17_traceSegment_059_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_059 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1215 20 20, g32p_row17_traceSegment_059_1215_0020, g32p_row17_traceSegment_059_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1255 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_059 1255 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1255 10 10, g32p_row17_traceSegment_059_1255_0010, g32p_row17_traceSegment_059_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_059 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_059 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_059_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_059 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1275 10 11, g32p_row17_traceSegment_059_1275_0010, g32p_row17_traceSegment_059_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_059 1255 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1255 20 21, g32p_row17_traceSegment_059_1255_0020, g32p_row17_traceSegment_059_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_059 1215 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1215 40 41, g32p_row17_traceSegment_059_1215_0040, g32p_row17_traceSegment_059_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_059_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_059 1134 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 1134 81 81, g32p_row17_traceSegment_059_1134_0081, g32p_row17_traceSegment_059_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_059 972 324 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 972 162 162, g32p_row17_traceSegment_059_0972_0162, g32p_row17_traceSegment_059_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_059 648 648 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 648 324 324, g32p_row17_traceSegment_059_0648_0324, g32p_row17_traceSegment_059_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_059_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_059 0 1296 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_059 0 648 648, g32p_row17_traceSegment_059_0000_0648, g32p_row17_traceSegment_059_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_059 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 59 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_059_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_064 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 64 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_064_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 10 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 0 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 0 10 10, g32p_row17_traceSegment_064_0000_0010, g32p_row17_traceSegment_064_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 20 10 10, g32p_row17_traceSegment_064_0020_0010, g32p_row17_traceSegment_064_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 0 40 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 0 20 20, g32p_row17_traceSegment_064_0000_0020, g32p_row17_traceSegment_064_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 40 10 10, g32p_row17_traceSegment_064_0040_0010, g32p_row17_traceSegment_064_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 60 10 11, g32p_row17_traceSegment_064_0060_0010, g32p_row17_traceSegment_064_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 40 20 21, g32p_row17_traceSegment_064_0040_0020, g32p_row17_traceSegment_064_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 0 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 0 40 41, g32p_row17_traceSegment_064_0000_0040, g32p_row17_traceSegment_064_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 81 10 10, g32p_row17_traceSegment_064_0081_0010, g32p_row17_traceSegment_064_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 101 10 10, g32p_row17_traceSegment_064_0101_0010, g32p_row17_traceSegment_064_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 81 20 20, g32p_row17_traceSegment_064_0081_0020, g32p_row17_traceSegment_064_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 121 10 10, g32p_row17_traceSegment_064_0121_0010, g32p_row17_traceSegment_064_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 141 10 11, g32p_row17_traceSegment_064_0141_0010, g32p_row17_traceSegment_064_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 121 20 21, g32p_row17_traceSegment_064_0121_0020, g32p_row17_traceSegment_064_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 81 40 41, g32p_row17_traceSegment_064_0081_0040, g32p_row17_traceSegment_064_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_064 0 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 0 81 81, g32p_row17_traceSegment_064_0000_0081, g32p_row17_traceSegment_064_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 162 10 10, g32p_row17_traceSegment_064_0162_0010, g32p_row17_traceSegment_064_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 182 10 10, g32p_row17_traceSegment_064_0182_0010, g32p_row17_traceSegment_064_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 162 20 20, g32p_row17_traceSegment_064_0162_0020, g32p_row17_traceSegment_064_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 202 10 10, g32p_row17_traceSegment_064_0202_0010, g32p_row17_traceSegment_064_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 232 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 222 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 222 10 11, g32p_row17_traceSegment_064_0222_0010, g32p_row17_traceSegment_064_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 202 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 202 20 21, g32p_row17_traceSegment_064_0202_0020, g32p_row17_traceSegment_064_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 162 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 162 40 41, g32p_row17_traceSegment_064_0162_0040, g32p_row17_traceSegment_064_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 243 10 10, g32p_row17_traceSegment_064_0243_0010, g32p_row17_traceSegment_064_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 263 10 10, g32p_row17_traceSegment_064_0263_0010, g32p_row17_traceSegment_064_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 243 20 20, g32p_row17_traceSegment_064_0243_0020, g32p_row17_traceSegment_064_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 283 10 10, g32p_row17_traceSegment_064_0283_0010, g32p_row17_traceSegment_064_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 303 10 11, g32p_row17_traceSegment_064_0303_0010, g32p_row17_traceSegment_064_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 283 20 21, g32p_row17_traceSegment_064_0283_0020, g32p_row17_traceSegment_064_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 243 40 41, g32p_row17_traceSegment_064_0243_0040, g32p_row17_traceSegment_064_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_064 162 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 162 81 81, g32p_row17_traceSegment_064_0162_0081, g32p_row17_traceSegment_064_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_064 0 324 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 0 162 162, g32p_row17_traceSegment_064_0000_0162, g32p_row17_traceSegment_064_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 334 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 324 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 324 10 10, g32p_row17_traceSegment_064_0324_0010, g32p_row17_traceSegment_064_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 344 10 10, g32p_row17_traceSegment_064_0344_0010, g32p_row17_traceSegment_064_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 324 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 324 20 20, g32p_row17_traceSegment_064_0324_0020, g32p_row17_traceSegment_064_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 364 10 10, g32p_row17_traceSegment_064_0364_0010, g32p_row17_traceSegment_064_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 384 10 11, g32p_row17_traceSegment_064_0384_0010, g32p_row17_traceSegment_064_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 364 20 21, g32p_row17_traceSegment_064_0364_0020, g32p_row17_traceSegment_064_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 324 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 324 40 41, g32p_row17_traceSegment_064_0324_0040, g32p_row17_traceSegment_064_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 405 10 10, g32p_row17_traceSegment_064_0405_0010, g32p_row17_traceSegment_064_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 425 10 10, g32p_row17_traceSegment_064_0425_0010, g32p_row17_traceSegment_064_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 405 20 20, g32p_row17_traceSegment_064_0405_0020, g32p_row17_traceSegment_064_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 445 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 445 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 445 10 10, g32p_row17_traceSegment_064_0445_0010, g32p_row17_traceSegment_064_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 475 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 465 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 465 10 11, g32p_row17_traceSegment_064_0465_0010, g32p_row17_traceSegment_064_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 445 41 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 445 20 21, g32p_row17_traceSegment_064_0445_0020, g32p_row17_traceSegment_064_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 405 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 405 40 41, g32p_row17_traceSegment_064_0405_0040, g32p_row17_traceSegment_064_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_064 324 162 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 324 81 81, g32p_row17_traceSegment_064_0324_0081, g32p_row17_traceSegment_064_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 496 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 486 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 486 10 10, g32p_row17_traceSegment_064_0486_0010, g32p_row17_traceSegment_064_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 506 10 10, g32p_row17_traceSegment_064_0506_0010, g32p_row17_traceSegment_064_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 486 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 486 20 20, g32p_row17_traceSegment_064_0486_0020, g32p_row17_traceSegment_064_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 526 10 10, g32p_row17_traceSegment_064_0526_0010, g32p_row17_traceSegment_064_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 546 10 11, g32p_row17_traceSegment_064_0546_0010, g32p_row17_traceSegment_064_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 526 20 21, g32p_row17_traceSegment_064_0526_0020, g32p_row17_traceSegment_064_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 486 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 486 40 41, g32p_row17_traceSegment_064_0486_0040, g32p_row17_traceSegment_064_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 577 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 567 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 567 10 10, g32p_row17_traceSegment_064_0567_0010, g32p_row17_traceSegment_064_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 587 10 10, g32p_row17_traceSegment_064_0587_0010, g32p_row17_traceSegment_064_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 567 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 567 20 20, g32p_row17_traceSegment_064_0567_0020, g32p_row17_traceSegment_064_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 607 10 10, g32p_row17_traceSegment_064_0607_0010, g32p_row17_traceSegment_064_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 627 10 11, g32p_row17_traceSegment_064_0627_0010, g32p_row17_traceSegment_064_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 607 20 21, g32p_row17_traceSegment_064_0607_0020, g32p_row17_traceSegment_064_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 567 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 567 40 41, g32p_row17_traceSegment_064_0567_0040, g32p_row17_traceSegment_064_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_064 486 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 486 81 81, g32p_row17_traceSegment_064_0486_0081, g32p_row17_traceSegment_064_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_064 324 324 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 324 162 162, g32p_row17_traceSegment_064_0324_0162, g32p_row17_traceSegment_064_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_064 0 648 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 0 324 324, g32p_row17_traceSegment_064_0000_0324, g32p_row17_traceSegment_064_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 648 10 10, g32p_row17_traceSegment_064_0648_0010, g32p_row17_traceSegment_064_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 678 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 668 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 668 10 10, g32p_row17_traceSegment_064_0668_0010, g32p_row17_traceSegment_064_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 648 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 648 20 20, g32p_row17_traceSegment_064_0648_0020, g32p_row17_traceSegment_064_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 688 10 10, g32p_row17_traceSegment_064_0688_0010, g32p_row17_traceSegment_064_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 708 10 11, g32p_row17_traceSegment_064_0708_0010, g32p_row17_traceSegment_064_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 688 20 21, g32p_row17_traceSegment_064_0688_0020, g32p_row17_traceSegment_064_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 648 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 648 40 41, g32p_row17_traceSegment_064_0648_0040, g32p_row17_traceSegment_064_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 729 10 10, g32p_row17_traceSegment_064_0729_0010, g32p_row17_traceSegment_064_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 749 10 10, g32p_row17_traceSegment_064_0749_0010, g32p_row17_traceSegment_064_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 729 20 20, g32p_row17_traceSegment_064_0729_0020, g32p_row17_traceSegment_064_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 779 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 769 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 769 10 10, g32p_row17_traceSegment_064_0769_0010, g32p_row17_traceSegment_064_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 789 10 11, g32p_row17_traceSegment_064_0789_0010, g32p_row17_traceSegment_064_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 769 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 769 20 21, g32p_row17_traceSegment_064_0769_0020, g32p_row17_traceSegment_064_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 729 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 729 40 41, g32p_row17_traceSegment_064_0729_0040, g32p_row17_traceSegment_064_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_064 648 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 648 81 81, g32p_row17_traceSegment_064_0648_0081, g32p_row17_traceSegment_064_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 810 10 10, g32p_row17_traceSegment_064_0810_0010, g32p_row17_traceSegment_064_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 830 10 10, g32p_row17_traceSegment_064_0830_0010, g32p_row17_traceSegment_064_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 810 20 20, g32p_row17_traceSegment_064_0810_0020, g32p_row17_traceSegment_064_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 850 10 10, g32p_row17_traceSegment_064_0850_0010, g32p_row17_traceSegment_064_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 870 10 11, g32p_row17_traceSegment_064_0870_0010, g32p_row17_traceSegment_064_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 850 20 21, g32p_row17_traceSegment_064_0850_0020, g32p_row17_traceSegment_064_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 810 40 41, g32p_row17_traceSegment_064_0810_0040, g32p_row17_traceSegment_064_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 891 10 10, g32p_row17_traceSegment_064_0891_0010, g32p_row17_traceSegment_064_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 911 10 10, g32p_row17_traceSegment_064_0911_0010, g32p_row17_traceSegment_064_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 891 20 20, g32p_row17_traceSegment_064_0891_0020, g32p_row17_traceSegment_064_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 931 10 10, g32p_row17_traceSegment_064_0931_0010, g32p_row17_traceSegment_064_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 951 10 11, g32p_row17_traceSegment_064_0951_0010, g32p_row17_traceSegment_064_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 931 20 21, g32p_row17_traceSegment_064_0931_0020, g32p_row17_traceSegment_064_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 891 40 41, g32p_row17_traceSegment_064_0891_0040, g32p_row17_traceSegment_064_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_064 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 810 81 81, g32p_row17_traceSegment_064_0810_0081, g32p_row17_traceSegment_064_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_064 648 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 648 162 162, g32p_row17_traceSegment_064_0648_0162, g32p_row17_traceSegment_064_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 972 10 10, g32p_row17_traceSegment_064_0972_0010, g32p_row17_traceSegment_064_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 992 10 10, g32p_row17_traceSegment_064_0992_0010, g32p_row17_traceSegment_064_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 972 20 20, g32p_row17_traceSegment_064_0972_0020, g32p_row17_traceSegment_064_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1012 10 10, g32p_row17_traceSegment_064_1012_0010, g32p_row17_traceSegment_064_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1032 10 11, g32p_row17_traceSegment_064_1032_0010, g32p_row17_traceSegment_064_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1012 20 21, g32p_row17_traceSegment_064_1012_0020, g32p_row17_traceSegment_064_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 972 40 41, g32p_row17_traceSegment_064_0972_0040, g32p_row17_traceSegment_064_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1053 10 10, g32p_row17_traceSegment_064_1053_0010, g32p_row17_traceSegment_064_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1073 10 10, g32p_row17_traceSegment_064_1073_0010, g32p_row17_traceSegment_064_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1053 20 20, g32p_row17_traceSegment_064_1053_0020, g32p_row17_traceSegment_064_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1093 10 10, g32p_row17_traceSegment_064_1093_0010, g32p_row17_traceSegment_064_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1113 10 11, g32p_row17_traceSegment_064_1113_0010, g32p_row17_traceSegment_064_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1093 20 21, g32p_row17_traceSegment_064_1093_0020, g32p_row17_traceSegment_064_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1053 40 41, g32p_row17_traceSegment_064_1053_0040, g32p_row17_traceSegment_064_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_064 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 972 81 81, g32p_row17_traceSegment_064_0972_0081, g32p_row17_traceSegment_064_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1134 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 1134 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1134 10 10, g32p_row17_traceSegment_064_1134_0010, g32p_row17_traceSegment_064_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1154 10 10, g32p_row17_traceSegment_064_1154_0010, g32p_row17_traceSegment_064_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 1134 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1134 20 20, g32p_row17_traceSegment_064_1134_0020, g32p_row17_traceSegment_064_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1174 10 10, g32p_row17_traceSegment_064_1174_0010, g32p_row17_traceSegment_064_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1194 10 11, g32p_row17_traceSegment_064_1194_0010, g32p_row17_traceSegment_064_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1174 20 21, g32p_row17_traceSegment_064_1174_0020, g32p_row17_traceSegment_064_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 1134 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1134 40 41, g32p_row17_traceSegment_064_1134_0040, g32p_row17_traceSegment_064_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1215 10 10, g32p_row17_traceSegment_064_1215_0010, g32p_row17_traceSegment_064_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1235 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 1235 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1235 10 10, g32p_row17_traceSegment_064_1235_0010, g32p_row17_traceSegment_064_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_064 1215 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1215 20 20, g32p_row17_traceSegment_064_1215_0020, g32p_row17_traceSegment_064_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_064 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1255 10 10, g32p_row17_traceSegment_064_1255_0010, g32p_row17_traceSegment_064_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_064 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_064 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_064_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_064 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1275 10 11, g32p_row17_traceSegment_064_1275_0010, g32p_row17_traceSegment_064_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_064 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1255 20 21, g32p_row17_traceSegment_064_1255_0020, g32p_row17_traceSegment_064_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_064 1215 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1215 40 41, g32p_row17_traceSegment_064_1215_0040, g32p_row17_traceSegment_064_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_064_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_064 1134 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 1134 81 81, g32p_row17_traceSegment_064_1134_0081, g32p_row17_traceSegment_064_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_064 972 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 972 162 162, g32p_row17_traceSegment_064_0972_0162, g32p_row17_traceSegment_064_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_064 648 648 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 648 324 324, g32p_row17_traceSegment_064_0648_0324, g32p_row17_traceSegment_064_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_064_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_064 0 1296 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_064 0 648 648, g32p_row17_traceSegment_064_0000_0648, g32p_row17_traceSegment_064_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_064 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 64 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_064_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_065 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 65 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_065_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 0 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 0 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 0 10 10, g32p_row17_traceSegment_065_0000_0010, g32p_row17_traceSegment_065_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 20 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 30 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 20 20 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 20 10 10, g32p_row17_traceSegment_065_0020_0010, g32p_row17_traceSegment_065_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 0 40 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 0 20 20, g32p_row17_traceSegment_065_0000_0020, g32p_row17_traceSegment_065_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 40 10 10, g32p_row17_traceSegment_065_0040_0010, g32p_row17_traceSegment_065_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 60 10 11, g32p_row17_traceSegment_065_0060_0010, g32p_row17_traceSegment_065_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 40 20 21, g32p_row17_traceSegment_065_0040_0020, g32p_row17_traceSegment_065_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 0 81 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 0 40 41, g32p_row17_traceSegment_065_0000_0040, g32p_row17_traceSegment_065_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 81 10 10, g32p_row17_traceSegment_065_0081_0010, g32p_row17_traceSegment_065_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 101 10 10, g32p_row17_traceSegment_065_0101_0010, g32p_row17_traceSegment_065_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 81 20 20, g32p_row17_traceSegment_065_0081_0020, g32p_row17_traceSegment_065_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 121 10 10, g32p_row17_traceSegment_065_0121_0010, g32p_row17_traceSegment_065_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 141 10 11, g32p_row17_traceSegment_065_0141_0010, g32p_row17_traceSegment_065_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 121 20 21, g32p_row17_traceSegment_065_0121_0020, g32p_row17_traceSegment_065_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 81 40 41, g32p_row17_traceSegment_065_0081_0040, g32p_row17_traceSegment_065_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_065 0 162 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 0 81 81, g32p_row17_traceSegment_065_0000_0081, g32p_row17_traceSegment_065_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 162 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 172 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 162 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 162 10 10, g32p_row17_traceSegment_065_0162_0010, g32p_row17_traceSegment_065_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 182 10 10, g32p_row17_traceSegment_065_0182_0010, g32p_row17_traceSegment_065_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 162 40 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 162 20 20, g32p_row17_traceSegment_065_0162_0020, g32p_row17_traceSegment_065_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 202 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 202 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 202 10 10, g32p_row17_traceSegment_065_0202_0010, g32p_row17_traceSegment_065_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 222 10 11, g32p_row17_traceSegment_065_0222_0010, g32p_row17_traceSegment_065_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 202 41 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 202 20 21, g32p_row17_traceSegment_065_0202_0020, g32p_row17_traceSegment_065_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 162 81 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 162 40 41, g32p_row17_traceSegment_065_0162_0040, g32p_row17_traceSegment_065_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 243 10 10, g32p_row17_traceSegment_065_0243_0010, g32p_row17_traceSegment_065_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 263 10 10, g32p_row17_traceSegment_065_0263_0010, g32p_row17_traceSegment_065_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 243 20 20, g32p_row17_traceSegment_065_0243_0020, g32p_row17_traceSegment_065_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 283 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 283 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 283 10 10, g32p_row17_traceSegment_065_0283_0010, g32p_row17_traceSegment_065_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 303 10 11, g32p_row17_traceSegment_065_0303_0010, g32p_row17_traceSegment_065_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 283 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 283 20 21, g32p_row17_traceSegment_065_0283_0020, g32p_row17_traceSegment_065_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 243 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 243 40 41, g32p_row17_traceSegment_065_0243_0040, g32p_row17_traceSegment_065_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_065 162 162 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 162 81 81, g32p_row17_traceSegment_065_0162_0081, g32p_row17_traceSegment_065_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_065 0 324 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 0 162 162, g32p_row17_traceSegment_065_0000_0162, g32p_row17_traceSegment_065_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 324 10 10, g32p_row17_traceSegment_065_0324_0010, g32p_row17_traceSegment_065_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 344 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 344 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 344 10 10, g32p_row17_traceSegment_065_0344_0010, g32p_row17_traceSegment_065_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 324 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 324 20 20, g32p_row17_traceSegment_065_0324_0020, g32p_row17_traceSegment_065_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 364 10 10, g32p_row17_traceSegment_065_0364_0010, g32p_row17_traceSegment_065_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 384 10 11, g32p_row17_traceSegment_065_0384_0010, g32p_row17_traceSegment_065_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 364 20 21, g32p_row17_traceSegment_065_0364_0020, g32p_row17_traceSegment_065_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 324 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 324 40 41, g32p_row17_traceSegment_065_0324_0040, g32p_row17_traceSegment_065_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 405 10 10, g32p_row17_traceSegment_065_0405_0010, g32p_row17_traceSegment_065_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 425 10 10, g32p_row17_traceSegment_065_0425_0010, g32p_row17_traceSegment_065_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 405 20 20, g32p_row17_traceSegment_065_0405_0020, g32p_row17_traceSegment_065_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 445 10 10, g32p_row17_traceSegment_065_0445_0010, g32p_row17_traceSegment_065_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 465 10 11, g32p_row17_traceSegment_065_0465_0010, g32p_row17_traceSegment_065_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 445 20 21, g32p_row17_traceSegment_065_0445_0020, g32p_row17_traceSegment_065_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 405 40 41, g32p_row17_traceSegment_065_0405_0040, g32p_row17_traceSegment_065_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_065 324 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 324 81 81, g32p_row17_traceSegment_065_0324_0081, g32p_row17_traceSegment_065_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 486 10 10, g32p_row17_traceSegment_065_0486_0010, g32p_row17_traceSegment_065_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 506 10 10, g32p_row17_traceSegment_065_0506_0010, g32p_row17_traceSegment_065_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 486 20 20, g32p_row17_traceSegment_065_0486_0020, g32p_row17_traceSegment_065_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 526 10 10, g32p_row17_traceSegment_065_0526_0010, g32p_row17_traceSegment_065_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 546 10 11, g32p_row17_traceSegment_065_0546_0010, g32p_row17_traceSegment_065_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 526 20 21, g32p_row17_traceSegment_065_0526_0020, g32p_row17_traceSegment_065_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 486 40 41, g32p_row17_traceSegment_065_0486_0040, g32p_row17_traceSegment_065_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 567 10 10, g32p_row17_traceSegment_065_0567_0010, g32p_row17_traceSegment_065_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 587 10 10, g32p_row17_traceSegment_065_0587_0010, g32p_row17_traceSegment_065_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 567 20 20, g32p_row17_traceSegment_065_0567_0020, g32p_row17_traceSegment_065_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 607 10 10, g32p_row17_traceSegment_065_0607_0010, g32p_row17_traceSegment_065_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 627 10 11, g32p_row17_traceSegment_065_0627_0010, g32p_row17_traceSegment_065_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 607 20 21, g32p_row17_traceSegment_065_0607_0020, g32p_row17_traceSegment_065_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 567 40 41, g32p_row17_traceSegment_065_0567_0040, g32p_row17_traceSegment_065_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_065 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 486 81 81, g32p_row17_traceSegment_065_0486_0081, g32p_row17_traceSegment_065_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_065 324 324 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 324 162 162, g32p_row17_traceSegment_065_0324_0162, g32p_row17_traceSegment_065_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_065 0 648 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 0 324 324, g32p_row17_traceSegment_065_0000_0324, g32p_row17_traceSegment_065_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 648 10 10, g32p_row17_traceSegment_065_0648_0010, g32p_row17_traceSegment_065_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 668 10 10, g32p_row17_traceSegment_065_0668_0010, g32p_row17_traceSegment_065_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 648 20 20, g32p_row17_traceSegment_065_0648_0020, g32p_row17_traceSegment_065_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 688 10 10, g32p_row17_traceSegment_065_0688_0010, g32p_row17_traceSegment_065_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 708 10 11, g32p_row17_traceSegment_065_0708_0010, g32p_row17_traceSegment_065_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 688 20 21, g32p_row17_traceSegment_065_0688_0020, g32p_row17_traceSegment_065_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 648 40 41, g32p_row17_traceSegment_065_0648_0040, g32p_row17_traceSegment_065_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 729 10 10, g32p_row17_traceSegment_065_0729_0010, g32p_row17_traceSegment_065_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 759 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 749 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 749 10 10, g32p_row17_traceSegment_065_0749_0010, g32p_row17_traceSegment_065_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 729 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 729 20 20, g32p_row17_traceSegment_065_0729_0020, g32p_row17_traceSegment_065_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 769 10 10, g32p_row17_traceSegment_065_0769_0010, g32p_row17_traceSegment_065_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 789 10 11, g32p_row17_traceSegment_065_0789_0010, g32p_row17_traceSegment_065_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 769 20 21, g32p_row17_traceSegment_065_0769_0020, g32p_row17_traceSegment_065_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 729 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 729 40 41, g32p_row17_traceSegment_065_0729_0040, g32p_row17_traceSegment_065_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_065 648 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 648 81 81, g32p_row17_traceSegment_065_0648_0081, g32p_row17_traceSegment_065_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 810 10 10, g32p_row17_traceSegment_065_0810_0010, g32p_row17_traceSegment_065_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 830 10 10, g32p_row17_traceSegment_065_0830_0010, g32p_row17_traceSegment_065_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 810 20 20, g32p_row17_traceSegment_065_0810_0020, g32p_row17_traceSegment_065_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 850 10 10, g32p_row17_traceSegment_065_0850_0010, g32p_row17_traceSegment_065_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 870 10 11, g32p_row17_traceSegment_065_0870_0010, g32p_row17_traceSegment_065_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 850 20 21, g32p_row17_traceSegment_065_0850_0020, g32p_row17_traceSegment_065_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 810 40 41, g32p_row17_traceSegment_065_0810_0040, g32p_row17_traceSegment_065_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 891 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 891 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 891 10 10, g32p_row17_traceSegment_065_0891_0010, g32p_row17_traceSegment_065_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 911 10 10, g32p_row17_traceSegment_065_0911_0010, g32p_row17_traceSegment_065_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 891 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 891 20 20, g32p_row17_traceSegment_065_0891_0020, g32p_row17_traceSegment_065_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 931 10 10, g32p_row17_traceSegment_065_0931_0010, g32p_row17_traceSegment_065_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 951 10 11, g32p_row17_traceSegment_065_0951_0010, g32p_row17_traceSegment_065_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 931 20 21, g32p_row17_traceSegment_065_0931_0020, g32p_row17_traceSegment_065_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 891 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 891 40 41, g32p_row17_traceSegment_065_0891_0040, g32p_row17_traceSegment_065_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_065 810 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 810 81 81, g32p_row17_traceSegment_065_0810_0081, g32p_row17_traceSegment_065_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_065 648 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 648 162 162, g32p_row17_traceSegment_065_0648_0162, g32p_row17_traceSegment_065_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 972 10 10, g32p_row17_traceSegment_065_0972_0010, g32p_row17_traceSegment_065_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 992 10 10, g32p_row17_traceSegment_065_0992_0010, g32p_row17_traceSegment_065_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 972 20 20, g32p_row17_traceSegment_065_0972_0020, g32p_row17_traceSegment_065_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1012 10 10, g32p_row17_traceSegment_065_1012_0010, g32p_row17_traceSegment_065_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1032 10 11, g32p_row17_traceSegment_065_1032_0010, g32p_row17_traceSegment_065_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1012 20 21, g32p_row17_traceSegment_065_1012_0020, g32p_row17_traceSegment_065_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 972 40 41, g32p_row17_traceSegment_065_0972_0040, g32p_row17_traceSegment_065_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1053 10 10, g32p_row17_traceSegment_065_1053_0010, g32p_row17_traceSegment_065_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1073 10 10, g32p_row17_traceSegment_065_1073_0010, g32p_row17_traceSegment_065_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1053 20 20, g32p_row17_traceSegment_065_1053_0020, g32p_row17_traceSegment_065_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1093 10 10, g32p_row17_traceSegment_065_1093_0010, g32p_row17_traceSegment_065_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1113 10 11, g32p_row17_traceSegment_065_1113_0010, g32p_row17_traceSegment_065_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1093 20 21, g32p_row17_traceSegment_065_1093_0020, g32p_row17_traceSegment_065_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1053 40 41, g32p_row17_traceSegment_065_1053_0040, g32p_row17_traceSegment_065_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_065 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 972 81 81, g32p_row17_traceSegment_065_0972_0081, g32p_row17_traceSegment_065_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1134 10 10, g32p_row17_traceSegment_065_1134_0010, g32p_row17_traceSegment_065_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1154 10 10, g32p_row17_traceSegment_065_1154_0010, g32p_row17_traceSegment_065_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1134 20 20, g32p_row17_traceSegment_065_1134_0020, g32p_row17_traceSegment_065_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1174 10 10, g32p_row17_traceSegment_065_1174_0010, g32p_row17_traceSegment_065_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1194 10 11, g32p_row17_traceSegment_065_1194_0010, g32p_row17_traceSegment_065_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1174 20 21, g32p_row17_traceSegment_065_1174_0020, g32p_row17_traceSegment_065_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1134 40 41, g32p_row17_traceSegment_065_1134_0040, g32p_row17_traceSegment_065_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1215 10 10, g32p_row17_traceSegment_065_1215_0010, g32p_row17_traceSegment_065_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1235 10 10, g32p_row17_traceSegment_065_1235_0010, g32p_row17_traceSegment_065_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_065 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1215 20 20, g32p_row17_traceSegment_065_1215_0020, g32p_row17_traceSegment_065_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_065 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1255 10 10, g32p_row17_traceSegment_065_1255_0010, g32p_row17_traceSegment_065_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_065 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_065 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_065_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_065 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1275 10 11, g32p_row17_traceSegment_065_1275_0010, g32p_row17_traceSegment_065_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_065 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1255 20 21, g32p_row17_traceSegment_065_1255_0020, g32p_row17_traceSegment_065_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_065 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1215 40 41, g32p_row17_traceSegment_065_1215_0040, g32p_row17_traceSegment_065_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_065_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_065 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 1134 81 81, g32p_row17_traceSegment_065_1134_0081, g32p_row17_traceSegment_065_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_065 972 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 972 162 162, g32p_row17_traceSegment_065_0972_0162, g32p_row17_traceSegment_065_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_065 648 648 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 648 324 324, g32p_row17_traceSegment_065_0648_0324, g32p_row17_traceSegment_065_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_065_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_065 0 1296 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_065 0 648 648, g32p_row17_traceSegment_065_0000_0648, g32p_row17_traceSegment_065_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 65 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_065_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_066 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 66 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_066_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 0 10 10, g32p_row17_traceSegment_066_0000_0010, g32p_row17_traceSegment_066_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 20 10 10, g32p_row17_traceSegment_066_0020_0010, g32p_row17_traceSegment_066_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 0 20 20, g32p_row17_traceSegment_066_0000_0020, g32p_row17_traceSegment_066_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 40 10 10, g32p_row17_traceSegment_066_0040_0010, g32p_row17_traceSegment_066_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 60 10 11, g32p_row17_traceSegment_066_0060_0010, g32p_row17_traceSegment_066_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 40 20 21, g32p_row17_traceSegment_066_0040_0020, g32p_row17_traceSegment_066_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 0 40 41, g32p_row17_traceSegment_066_0000_0040, g32p_row17_traceSegment_066_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 81 10 10, g32p_row17_traceSegment_066_0081_0010, g32p_row17_traceSegment_066_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 101 10 10, g32p_row17_traceSegment_066_0101_0010, g32p_row17_traceSegment_066_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 81 20 20, g32p_row17_traceSegment_066_0081_0020, g32p_row17_traceSegment_066_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 121 10 10, g32p_row17_traceSegment_066_0121_0010, g32p_row17_traceSegment_066_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 141 10 11, g32p_row17_traceSegment_066_0141_0010, g32p_row17_traceSegment_066_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 121 20 21, g32p_row17_traceSegment_066_0121_0020, g32p_row17_traceSegment_066_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 81 40 41, g32p_row17_traceSegment_066_0081_0040, g32p_row17_traceSegment_066_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_066 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 0 81 81, g32p_row17_traceSegment_066_0000_0081, g32p_row17_traceSegment_066_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 162 10 10, g32p_row17_traceSegment_066_0162_0010, g32p_row17_traceSegment_066_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 182 10 10, g32p_row17_traceSegment_066_0182_0010, g32p_row17_traceSegment_066_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 162 20 20, g32p_row17_traceSegment_066_0162_0020, g32p_row17_traceSegment_066_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 202 10 10, g32p_row17_traceSegment_066_0202_0010, g32p_row17_traceSegment_066_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 222 10 11, g32p_row17_traceSegment_066_0222_0010, g32p_row17_traceSegment_066_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 202 20 21, g32p_row17_traceSegment_066_0202_0020, g32p_row17_traceSegment_066_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 162 40 41, g32p_row17_traceSegment_066_0162_0040, g32p_row17_traceSegment_066_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 243 10 10, g32p_row17_traceSegment_066_0243_0010, g32p_row17_traceSegment_066_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 263 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 263 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 263 10 10, g32p_row17_traceSegment_066_0263_0010, g32p_row17_traceSegment_066_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 243 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 243 20 20, g32p_row17_traceSegment_066_0243_0020, g32p_row17_traceSegment_066_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 283 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 283 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 283 10 10, g32p_row17_traceSegment_066_0283_0010, g32p_row17_traceSegment_066_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 303 10 11, g32p_row17_traceSegment_066_0303_0010, g32p_row17_traceSegment_066_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 283 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 283 20 21, g32p_row17_traceSegment_066_0283_0020, g32p_row17_traceSegment_066_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 243 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 243 40 41, g32p_row17_traceSegment_066_0243_0040, g32p_row17_traceSegment_066_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_066 162 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 162 81 81, g32p_row17_traceSegment_066_0162_0081, g32p_row17_traceSegment_066_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_066 0 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 0 162 162, g32p_row17_traceSegment_066_0000_0162, g32p_row17_traceSegment_066_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 324 10 10, g32p_row17_traceSegment_066_0324_0010, g32p_row17_traceSegment_066_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 344 10 10, g32p_row17_traceSegment_066_0344_0010, g32p_row17_traceSegment_066_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 324 20 20, g32p_row17_traceSegment_066_0324_0020, g32p_row17_traceSegment_066_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 374 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 364 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 364 10 10, g32p_row17_traceSegment_066_0364_0010, g32p_row17_traceSegment_066_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 384 10 11, g32p_row17_traceSegment_066_0384_0010, g32p_row17_traceSegment_066_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 364 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 364 20 21, g32p_row17_traceSegment_066_0364_0020, g32p_row17_traceSegment_066_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 324 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 324 40 41, g32p_row17_traceSegment_066_0324_0040, g32p_row17_traceSegment_066_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 405 10 10, g32p_row17_traceSegment_066_0405_0010, g32p_row17_traceSegment_066_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 425 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 425 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 425 10 10, g32p_row17_traceSegment_066_0425_0010, g32p_row17_traceSegment_066_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 405 40 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 405 20 20, g32p_row17_traceSegment_066_0405_0020, g32p_row17_traceSegment_066_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 445 10 10, g32p_row17_traceSegment_066_0445_0010, g32p_row17_traceSegment_066_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 465 10 11, g32p_row17_traceSegment_066_0465_0010, g32p_row17_traceSegment_066_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 445 20 21, g32p_row17_traceSegment_066_0445_0020, g32p_row17_traceSegment_066_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 405 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 405 40 41, g32p_row17_traceSegment_066_0405_0040, g32p_row17_traceSegment_066_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_066 324 162 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 324 81 81, g32p_row17_traceSegment_066_0324_0081, g32p_row17_traceSegment_066_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 486 10 10, g32p_row17_traceSegment_066_0486_0010, g32p_row17_traceSegment_066_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 506 10 10, g32p_row17_traceSegment_066_0506_0010, g32p_row17_traceSegment_066_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 486 20 20, g32p_row17_traceSegment_066_0486_0020, g32p_row17_traceSegment_066_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 526 10 10, g32p_row17_traceSegment_066_0526_0010, g32p_row17_traceSegment_066_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 546 10 11, g32p_row17_traceSegment_066_0546_0010, g32p_row17_traceSegment_066_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 526 20 21, g32p_row17_traceSegment_066_0526_0020, g32p_row17_traceSegment_066_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 486 40 41, g32p_row17_traceSegment_066_0486_0040, g32p_row17_traceSegment_066_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 567 10 10, g32p_row17_traceSegment_066_0567_0010, g32p_row17_traceSegment_066_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 587 10 10, g32p_row17_traceSegment_066_0587_0010, g32p_row17_traceSegment_066_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 567 20 20, g32p_row17_traceSegment_066_0567_0020, g32p_row17_traceSegment_066_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 607 10 10, g32p_row17_traceSegment_066_0607_0010, g32p_row17_traceSegment_066_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 627 10 11, g32p_row17_traceSegment_066_0627_0010, g32p_row17_traceSegment_066_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 607 20 21, g32p_row17_traceSegment_066_0607_0020, g32p_row17_traceSegment_066_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 567 40 41, g32p_row17_traceSegment_066_0567_0040, g32p_row17_traceSegment_066_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_066 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 486 81 81, g32p_row17_traceSegment_066_0486_0081, g32p_row17_traceSegment_066_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_066 324 324 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 324 162 162, g32p_row17_traceSegment_066_0324_0162, g32p_row17_traceSegment_066_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_066 0 648 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 0 324 324, g32p_row17_traceSegment_066_0000_0324, g32p_row17_traceSegment_066_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 648 10 10, g32p_row17_traceSegment_066_0648_0010, g32p_row17_traceSegment_066_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 668 10 10, g32p_row17_traceSegment_066_0668_0010, g32p_row17_traceSegment_066_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 648 20 20, g32p_row17_traceSegment_066_0648_0020, g32p_row17_traceSegment_066_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 688 10 10, g32p_row17_traceSegment_066_0688_0010, g32p_row17_traceSegment_066_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 708 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 708 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 708 10 11, g32p_row17_traceSegment_066_0708_0010, g32p_row17_traceSegment_066_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 688 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 688 20 21, g32p_row17_traceSegment_066_0688_0020, g32p_row17_traceSegment_066_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 648 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 648 40 41, g32p_row17_traceSegment_066_0648_0040, g32p_row17_traceSegment_066_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 729 10 10, g32p_row17_traceSegment_066_0729_0010, g32p_row17_traceSegment_066_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 749 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 759 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 749 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 749 10 10, g32p_row17_traceSegment_066_0749_0010, g32p_row17_traceSegment_066_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 729 40 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 729 20 20, g32p_row17_traceSegment_066_0729_0020, g32p_row17_traceSegment_066_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 769 10 10, g32p_row17_traceSegment_066_0769_0010, g32p_row17_traceSegment_066_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 789 10 11, g32p_row17_traceSegment_066_0789_0010, g32p_row17_traceSegment_066_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 769 20 21, g32p_row17_traceSegment_066_0769_0020, g32p_row17_traceSegment_066_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 729 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 729 40 41, g32p_row17_traceSegment_066_0729_0040, g32p_row17_traceSegment_066_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_066 648 162 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 648 81 81, g32p_row17_traceSegment_066_0648_0081, g32p_row17_traceSegment_066_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 820 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 810 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 810 10 10, g32p_row17_traceSegment_066_0810_0010, g32p_row17_traceSegment_066_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 830 10 10, g32p_row17_traceSegment_066_0830_0010, g32p_row17_traceSegment_066_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 810 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 810 20 20, g32p_row17_traceSegment_066_0810_0020, g32p_row17_traceSegment_066_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 850 10 10, g32p_row17_traceSegment_066_0850_0010, g32p_row17_traceSegment_066_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 870 10 11, g32p_row17_traceSegment_066_0870_0010, g32p_row17_traceSegment_066_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 850 20 21, g32p_row17_traceSegment_066_0850_0020, g32p_row17_traceSegment_066_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 810 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 810 40 41, g32p_row17_traceSegment_066_0810_0040, g32p_row17_traceSegment_066_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 891 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 891 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 891 10 10, g32p_row17_traceSegment_066_0891_0010, g32p_row17_traceSegment_066_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 911 10 10, g32p_row17_traceSegment_066_0911_0010, g32p_row17_traceSegment_066_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 891 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 891 20 20, g32p_row17_traceSegment_066_0891_0020, g32p_row17_traceSegment_066_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 931 10 10, g32p_row17_traceSegment_066_0931_0010, g32p_row17_traceSegment_066_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 951 10 11, g32p_row17_traceSegment_066_0951_0010, g32p_row17_traceSegment_066_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 931 20 21, g32p_row17_traceSegment_066_0931_0020, g32p_row17_traceSegment_066_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 891 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 891 40 41, g32p_row17_traceSegment_066_0891_0040, g32p_row17_traceSegment_066_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_066 810 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 810 81 81, g32p_row17_traceSegment_066_0810_0081, g32p_row17_traceSegment_066_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_066 648 324 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 648 162 162, g32p_row17_traceSegment_066_0648_0162, g32p_row17_traceSegment_066_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 972 10 10, g32p_row17_traceSegment_066_0972_0010, g32p_row17_traceSegment_066_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 992 10 10, g32p_row17_traceSegment_066_0992_0010, g32p_row17_traceSegment_066_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 972 20 20, g32p_row17_traceSegment_066_0972_0020, g32p_row17_traceSegment_066_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1012 10 10, g32p_row17_traceSegment_066_1012_0010, g32p_row17_traceSegment_066_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1032 10 11, g32p_row17_traceSegment_066_1032_0010, g32p_row17_traceSegment_066_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1012 20 21, g32p_row17_traceSegment_066_1012_0020, g32p_row17_traceSegment_066_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 972 40 41, g32p_row17_traceSegment_066_0972_0040, g32p_row17_traceSegment_066_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1053 10 10, g32p_row17_traceSegment_066_1053_0010, g32p_row17_traceSegment_066_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1073 10 10, g32p_row17_traceSegment_066_1073_0010, g32p_row17_traceSegment_066_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1053 20 20, g32p_row17_traceSegment_066_1053_0020, g32p_row17_traceSegment_066_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1093 10 10, g32p_row17_traceSegment_066_1093_0010, g32p_row17_traceSegment_066_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1113 10 11, g32p_row17_traceSegment_066_1113_0010, g32p_row17_traceSegment_066_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1093 20 21, g32p_row17_traceSegment_066_1093_0020, g32p_row17_traceSegment_066_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1053 40 41, g32p_row17_traceSegment_066_1053_0040, g32p_row17_traceSegment_066_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_066 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 972 81 81, g32p_row17_traceSegment_066_0972_0081, g32p_row17_traceSegment_066_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1144 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 1134 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1134 10 10, g32p_row17_traceSegment_066_1134_0010, g32p_row17_traceSegment_066_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1154 10 10, g32p_row17_traceSegment_066_1154_0010, g32p_row17_traceSegment_066_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 1134 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1134 20 20, g32p_row17_traceSegment_066_1134_0020, g32p_row17_traceSegment_066_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1174 10 10, g32p_row17_traceSegment_066_1174_0010, g32p_row17_traceSegment_066_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1194 10 11, g32p_row17_traceSegment_066_1194_0010, g32p_row17_traceSegment_066_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1174 20 21, g32p_row17_traceSegment_066_1174_0020, g32p_row17_traceSegment_066_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 1134 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1134 40 41, g32p_row17_traceSegment_066_1134_0040, g32p_row17_traceSegment_066_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1215 10 10, g32p_row17_traceSegment_066_1215_0010, g32p_row17_traceSegment_066_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1235 10 10, g32p_row17_traceSegment_066_1235_0010, g32p_row17_traceSegment_066_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_066 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1215 20 20, g32p_row17_traceSegment_066_1215_0020, g32p_row17_traceSegment_066_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1265 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_066 1255 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1255 10 10, g32p_row17_traceSegment_066_1255_0010, g32p_row17_traceSegment_066_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_066 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_066 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_066_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_066 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1275 10 11, g32p_row17_traceSegment_066_1275_0010, g32p_row17_traceSegment_066_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_066 1255 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1255 20 21, g32p_row17_traceSegment_066_1255_0020, g32p_row17_traceSegment_066_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_066 1215 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1215 40 41, g32p_row17_traceSegment_066_1215_0040, g32p_row17_traceSegment_066_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_066_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_066 1134 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 1134 81 81, g32p_row17_traceSegment_066_1134_0081, g32p_row17_traceSegment_066_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_066 972 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 972 162 162, g32p_row17_traceSegment_066_0972_0162, g32p_row17_traceSegment_066_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_066 648 648 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 648 324 324, g32p_row17_traceSegment_066_0648_0324, g32p_row17_traceSegment_066_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_066_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_066 0 1296 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_066 0 648 648, g32p_row17_traceSegment_066_0000_0648, g32p_row17_traceSegment_066_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_066 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 66 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_066_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_067 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 67 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_067_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 0 10 10, g32p_row17_traceSegment_067_0000_0010, g32p_row17_traceSegment_067_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 20 10 10, g32p_row17_traceSegment_067_0020_0010, g32p_row17_traceSegment_067_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 0 20 20, g32p_row17_traceSegment_067_0000_0020, g32p_row17_traceSegment_067_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 40 10 10, g32p_row17_traceSegment_067_0040_0010, g32p_row17_traceSegment_067_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 60 10 11, g32p_row17_traceSegment_067_0060_0010, g32p_row17_traceSegment_067_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 40 20 21, g32p_row17_traceSegment_067_0040_0020, g32p_row17_traceSegment_067_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 0 40 41, g32p_row17_traceSegment_067_0000_0040, g32p_row17_traceSegment_067_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 81 10 10, g32p_row17_traceSegment_067_0081_0010, g32p_row17_traceSegment_067_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 101 10 10, g32p_row17_traceSegment_067_0101_0010, g32p_row17_traceSegment_067_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 81 20 20, g32p_row17_traceSegment_067_0081_0020, g32p_row17_traceSegment_067_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 121 10 10, g32p_row17_traceSegment_067_0121_0010, g32p_row17_traceSegment_067_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 141 10 11, g32p_row17_traceSegment_067_0141_0010, g32p_row17_traceSegment_067_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 121 20 21, g32p_row17_traceSegment_067_0121_0020, g32p_row17_traceSegment_067_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 81 40 41, g32p_row17_traceSegment_067_0081_0040, g32p_row17_traceSegment_067_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_067 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 0 81 81, g32p_row17_traceSegment_067_0000_0081, g32p_row17_traceSegment_067_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 162 10 10, g32p_row17_traceSegment_067_0162_0010, g32p_row17_traceSegment_067_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 182 10 10, g32p_row17_traceSegment_067_0182_0010, g32p_row17_traceSegment_067_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 162 20 20, g32p_row17_traceSegment_067_0162_0020, g32p_row17_traceSegment_067_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 202 10 10, g32p_row17_traceSegment_067_0202_0010, g32p_row17_traceSegment_067_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 222 10 11, g32p_row17_traceSegment_067_0222_0010, g32p_row17_traceSegment_067_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 202 20 21, g32p_row17_traceSegment_067_0202_0020, g32p_row17_traceSegment_067_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 162 40 41, g32p_row17_traceSegment_067_0162_0040, g32p_row17_traceSegment_067_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 243 10 10, g32p_row17_traceSegment_067_0243_0010, g32p_row17_traceSegment_067_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 263 10 10, g32p_row17_traceSegment_067_0263_0010, g32p_row17_traceSegment_067_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 243 20 20, g32p_row17_traceSegment_067_0243_0020, g32p_row17_traceSegment_067_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 283 10 10, g32p_row17_traceSegment_067_0283_0010, g32p_row17_traceSegment_067_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 303 10 11, g32p_row17_traceSegment_067_0303_0010, g32p_row17_traceSegment_067_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 283 20 21, g32p_row17_traceSegment_067_0283_0020, g32p_row17_traceSegment_067_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 243 40 41, g32p_row17_traceSegment_067_0243_0040, g32p_row17_traceSegment_067_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_067 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 162 81 81, g32p_row17_traceSegment_067_0162_0081, g32p_row17_traceSegment_067_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_067 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 0 162 162, g32p_row17_traceSegment_067_0000_0162, g32p_row17_traceSegment_067_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 324 10 10, g32p_row17_traceSegment_067_0324_0010, g32p_row17_traceSegment_067_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 344 10 10, g32p_row17_traceSegment_067_0344_0010, g32p_row17_traceSegment_067_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 324 20 20, g32p_row17_traceSegment_067_0324_0020, g32p_row17_traceSegment_067_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 364 10 10, g32p_row17_traceSegment_067_0364_0010, g32p_row17_traceSegment_067_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 384 10 11, g32p_row17_traceSegment_067_0384_0010, g32p_row17_traceSegment_067_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 364 20 21, g32p_row17_traceSegment_067_0364_0020, g32p_row17_traceSegment_067_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 324 40 41, g32p_row17_traceSegment_067_0324_0040, g32p_row17_traceSegment_067_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 405 10 10, g32p_row17_traceSegment_067_0405_0010, g32p_row17_traceSegment_067_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 425 10 10, g32p_row17_traceSegment_067_0425_0010, g32p_row17_traceSegment_067_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 405 20 20, g32p_row17_traceSegment_067_0405_0020, g32p_row17_traceSegment_067_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 445 10 10, g32p_row17_traceSegment_067_0445_0010, g32p_row17_traceSegment_067_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 465 10 11, g32p_row17_traceSegment_067_0465_0010, g32p_row17_traceSegment_067_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 445 20 21, g32p_row17_traceSegment_067_0445_0020, g32p_row17_traceSegment_067_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 405 40 41, g32p_row17_traceSegment_067_0405_0040, g32p_row17_traceSegment_067_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_067 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 324 81 81, g32p_row17_traceSegment_067_0324_0081, g32p_row17_traceSegment_067_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 486 10 10, g32p_row17_traceSegment_067_0486_0010, g32p_row17_traceSegment_067_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 506 10 10, g32p_row17_traceSegment_067_0506_0010, g32p_row17_traceSegment_067_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 486 20 20, g32p_row17_traceSegment_067_0486_0020, g32p_row17_traceSegment_067_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 526 10 10, g32p_row17_traceSegment_067_0526_0010, g32p_row17_traceSegment_067_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 546 10 11, g32p_row17_traceSegment_067_0546_0010, g32p_row17_traceSegment_067_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 526 20 21, g32p_row17_traceSegment_067_0526_0020, g32p_row17_traceSegment_067_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 486 40 41, g32p_row17_traceSegment_067_0486_0040, g32p_row17_traceSegment_067_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 567 10 10, g32p_row17_traceSegment_067_0567_0010, g32p_row17_traceSegment_067_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 587 10 10, g32p_row17_traceSegment_067_0587_0010, g32p_row17_traceSegment_067_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 567 20 20, g32p_row17_traceSegment_067_0567_0020, g32p_row17_traceSegment_067_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 607 10 10, g32p_row17_traceSegment_067_0607_0010, g32p_row17_traceSegment_067_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 627 10 11, g32p_row17_traceSegment_067_0627_0010, g32p_row17_traceSegment_067_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 607 20 21, g32p_row17_traceSegment_067_0607_0020, g32p_row17_traceSegment_067_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 567 40 41, g32p_row17_traceSegment_067_0567_0040, g32p_row17_traceSegment_067_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_067 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 486 81 81, g32p_row17_traceSegment_067_0486_0081, g32p_row17_traceSegment_067_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_067 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 324 162 162, g32p_row17_traceSegment_067_0324_0162, g32p_row17_traceSegment_067_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_067 0 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 0 324 324, g32p_row17_traceSegment_067_0000_0324, g32p_row17_traceSegment_067_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 648 10 10, g32p_row17_traceSegment_067_0648_0010, g32p_row17_traceSegment_067_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 668 10 10, g32p_row17_traceSegment_067_0668_0010, g32p_row17_traceSegment_067_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 648 20 20, g32p_row17_traceSegment_067_0648_0020, g32p_row17_traceSegment_067_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 688 10 10, g32p_row17_traceSegment_067_0688_0010, g32p_row17_traceSegment_067_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 708 10 11, g32p_row17_traceSegment_067_0708_0010, g32p_row17_traceSegment_067_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 688 20 21, g32p_row17_traceSegment_067_0688_0020, g32p_row17_traceSegment_067_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 648 40 41, g32p_row17_traceSegment_067_0648_0040, g32p_row17_traceSegment_067_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 729 10 10, g32p_row17_traceSegment_067_0729_0010, g32p_row17_traceSegment_067_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 749 10 10, g32p_row17_traceSegment_067_0749_0010, g32p_row17_traceSegment_067_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 729 20 20, g32p_row17_traceSegment_067_0729_0020, g32p_row17_traceSegment_067_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 769 10 10, g32p_row17_traceSegment_067_0769_0010, g32p_row17_traceSegment_067_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 789 10 11, g32p_row17_traceSegment_067_0789_0010, g32p_row17_traceSegment_067_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 769 20 21, g32p_row17_traceSegment_067_0769_0020, g32p_row17_traceSegment_067_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 729 40 41, g32p_row17_traceSegment_067_0729_0040, g32p_row17_traceSegment_067_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_067 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 648 81 81, g32p_row17_traceSegment_067_0648_0081, g32p_row17_traceSegment_067_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 810 10 10, g32p_row17_traceSegment_067_0810_0010, g32p_row17_traceSegment_067_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 830 10 10, g32p_row17_traceSegment_067_0830_0010, g32p_row17_traceSegment_067_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 810 20 20, g32p_row17_traceSegment_067_0810_0020, g32p_row17_traceSegment_067_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 860 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 850 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 850 10 10, g32p_row17_traceSegment_067_0850_0010, g32p_row17_traceSegment_067_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 870 10 11, g32p_row17_traceSegment_067_0870_0010, g32p_row17_traceSegment_067_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 850 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 850 20 21, g32p_row17_traceSegment_067_0850_0020, g32p_row17_traceSegment_067_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 810 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 810 40 41, g32p_row17_traceSegment_067_0810_0040, g32p_row17_traceSegment_067_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 891 10 10, g32p_row17_traceSegment_067_0891_0010, g32p_row17_traceSegment_067_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 911 10 10, g32p_row17_traceSegment_067_0911_0010, g32p_row17_traceSegment_067_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 891 20 20, g32p_row17_traceSegment_067_0891_0020, g32p_row17_traceSegment_067_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 931 10 10, g32p_row17_traceSegment_067_0931_0010, g32p_row17_traceSegment_067_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 951 10 11, g32p_row17_traceSegment_067_0951_0010, g32p_row17_traceSegment_067_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 931 20 21, g32p_row17_traceSegment_067_0931_0020, g32p_row17_traceSegment_067_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 891 40 41, g32p_row17_traceSegment_067_0891_0040, g32p_row17_traceSegment_067_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_067 810 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 810 81 81, g32p_row17_traceSegment_067_0810_0081, g32p_row17_traceSegment_067_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_067 648 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 648 162 162, g32p_row17_traceSegment_067_0648_0162, g32p_row17_traceSegment_067_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 972 10 10, g32p_row17_traceSegment_067_0972_0010, g32p_row17_traceSegment_067_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 992 10 10, g32p_row17_traceSegment_067_0992_0010, g32p_row17_traceSegment_067_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 972 20 20, g32p_row17_traceSegment_067_0972_0020, g32p_row17_traceSegment_067_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1022 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 1012 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1012 10 10, g32p_row17_traceSegment_067_1012_0010, g32p_row17_traceSegment_067_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1032 10 11, g32p_row17_traceSegment_067_1032_0010, g32p_row17_traceSegment_067_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 1012 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1012 20 21, g32p_row17_traceSegment_067_1012_0020, g32p_row17_traceSegment_067_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 972 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 972 40 41, g32p_row17_traceSegment_067_0972_0040, g32p_row17_traceSegment_067_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1053 10 10, g32p_row17_traceSegment_067_1053_0010, g32p_row17_traceSegment_067_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1073 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 1073 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1073 10 10, g32p_row17_traceSegment_067_1073_0010, g32p_row17_traceSegment_067_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 1053 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1053 20 20, g32p_row17_traceSegment_067_1053_0020, g32p_row17_traceSegment_067_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1093 10 10, g32p_row17_traceSegment_067_1093_0010, g32p_row17_traceSegment_067_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1113 10 11, g32p_row17_traceSegment_067_1113_0010, g32p_row17_traceSegment_067_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1093 20 21, g32p_row17_traceSegment_067_1093_0020, g32p_row17_traceSegment_067_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 1053 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1053 40 41, g32p_row17_traceSegment_067_1053_0040, g32p_row17_traceSegment_067_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_067 972 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 972 81 81, g32p_row17_traceSegment_067_0972_0081, g32p_row17_traceSegment_067_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1144 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 1134 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1134 10 10, g32p_row17_traceSegment_067_1134_0010, g32p_row17_traceSegment_067_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1154 10 10, g32p_row17_traceSegment_067_1154_0010, g32p_row17_traceSegment_067_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 1134 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1134 20 20, g32p_row17_traceSegment_067_1134_0020, g32p_row17_traceSegment_067_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1174 10 10, g32p_row17_traceSegment_067_1174_0010, g32p_row17_traceSegment_067_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1194 10 11, g32p_row17_traceSegment_067_1194_0010, g32p_row17_traceSegment_067_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1174 20 21, g32p_row17_traceSegment_067_1174_0020, g32p_row17_traceSegment_067_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 1134 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1134 40 41, g32p_row17_traceSegment_067_1134_0040, g32p_row17_traceSegment_067_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1215 10 10, g32p_row17_traceSegment_067_1215_0010, g32p_row17_traceSegment_067_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1235 10 10, g32p_row17_traceSegment_067_1235_0010, g32p_row17_traceSegment_067_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_067 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1215 20 20, g32p_row17_traceSegment_067_1215_0020, g32p_row17_traceSegment_067_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_067 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1255 10 10, g32p_row17_traceSegment_067_1255_0010, g32p_row17_traceSegment_067_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_067 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_067 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_067_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_067 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1275 10 11, g32p_row17_traceSegment_067_1275_0010, g32p_row17_traceSegment_067_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_067 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1255 20 21, g32p_row17_traceSegment_067_1255_0020, g32p_row17_traceSegment_067_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_067 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1215 40 41, g32p_row17_traceSegment_067_1215_0040, g32p_row17_traceSegment_067_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_067_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_067 1134 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 1134 81 81, g32p_row17_traceSegment_067_1134_0081, g32p_row17_traceSegment_067_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_067 972 324 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 972 162 162, g32p_row17_traceSegment_067_0972_0162, g32p_row17_traceSegment_067_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_067 648 648 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 648 324 324, g32p_row17_traceSegment_067_0648_0324, g32p_row17_traceSegment_067_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_067_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_067 0 1296 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_067 0 648 648, g32p_row17_traceSegment_067_0000_0648, g32p_row17_traceSegment_067_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 67 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_067_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_tracePolynomial_051 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 51) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 51) (g32p_literalTraceValue 16 51)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_051]
  decide +kernel

theorem g32p_row17_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 56) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 56) (g32p_literalTraceValue 16 56)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_056]
  decide +kernel

theorem g32p_row17_tracePolynomial_057 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 57) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 57) (g32p_literalTraceValue 16 57)
      [1, -1, 1] [-2592] = true := by
  rw [g32p_row17_traceCoefficients_057]
  decide +kernel

theorem g32p_row17_tracePolynomial_059 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 59) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 59) (g32p_literalTraceValue 16 59)
      [1, -1, 1] [1296, 1296, 1296] = true := by
  rw [g32p_row17_traceCoefficients_059]
  decide +kernel

theorem g32p_row17_tracePolynomial_064 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 64) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 64) (g32p_literalTraceValue 16 64)
      [1, -1, 1] [5184, 5184, 5184] = true := by
  rw [g32p_row17_traceCoefficients_064]
  decide +kernel

theorem g32p_row17_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 65) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 65) (g32p_literalTraceValue 16 65)
      [1, -1, 1] [20736, 20736, 20736] = true := by
  rw [g32p_row17_traceCoefficients_065]
  decide +kernel

theorem g32p_row17_tracePolynomial_066 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 66) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 66) (g32p_literalTraceValue 16 66)
      [1, -1, 1] [1296, 1296, 1296] = true := by
  rw [g32p_row17_traceCoefficients_066]
  decide +kernel

theorem g32p_row17_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 67) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 67) (g32p_literalTraceValue 16 67)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_067]
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

private def g32p_row17_traceSegment_069 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 69 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_069_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 0 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 0 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 0 10 10, g32p_row17_traceSegment_069_0000_0010, g32p_row17_traceSegment_069_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 20 10 10, g32p_row17_traceSegment_069_0020_0010, g32p_row17_traceSegment_069_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 0 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 0 20 20, g32p_row17_traceSegment_069_0000_0020, g32p_row17_traceSegment_069_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 40 10 10, g32p_row17_traceSegment_069_0040_0010, g32p_row17_traceSegment_069_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 60 10 11, g32p_row17_traceSegment_069_0060_0010, g32p_row17_traceSegment_069_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 40 20 21, g32p_row17_traceSegment_069_0040_0020, g32p_row17_traceSegment_069_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 0 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 0 40 41, g32p_row17_traceSegment_069_0000_0040, g32p_row17_traceSegment_069_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 81 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 91 10 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 81 20 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 81 10 10, g32p_row17_traceSegment_069_0081_0010, g32p_row17_traceSegment_069_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 111 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 101 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 101 10 10, g32p_row17_traceSegment_069_0101_0010, g32p_row17_traceSegment_069_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 81 40 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 81 20 20, g32p_row17_traceSegment_069_0081_0020, g32p_row17_traceSegment_069_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 121 10 10, g32p_row17_traceSegment_069_0121_0010, g32p_row17_traceSegment_069_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 141 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 151 11 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 141 21 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 141 10 11, g32p_row17_traceSegment_069_0141_0010, g32p_row17_traceSegment_069_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 121 41 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 121 20 21, g32p_row17_traceSegment_069_0121_0020, g32p_row17_traceSegment_069_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 81 81 = [2, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 81 40 41, g32p_row17_traceSegment_069_0081_0040, g32p_row17_traceSegment_069_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_069 0 162 = [3, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 0 81 81, g32p_row17_traceSegment_069_0000_0081, g32p_row17_traceSegment_069_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 162 10 10, g32p_row17_traceSegment_069_0162_0010, g32p_row17_traceSegment_069_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 182 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 192 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 182 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 182 10 10, g32p_row17_traceSegment_069_0182_0010, g32p_row17_traceSegment_069_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 162 40 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 162 20 20, g32p_row17_traceSegment_069_0162_0020, g32p_row17_traceSegment_069_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 202 10 10, g32p_row17_traceSegment_069_0202_0010, g32p_row17_traceSegment_069_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 232 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 222 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 222 10 11, g32p_row17_traceSegment_069_0222_0010, g32p_row17_traceSegment_069_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 202 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 202 20 21, g32p_row17_traceSegment_069_0202_0020, g32p_row17_traceSegment_069_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 162 81 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 162 40 41, g32p_row17_traceSegment_069_0162_0040, g32p_row17_traceSegment_069_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 243 10 10, g32p_row17_traceSegment_069_0243_0010, g32p_row17_traceSegment_069_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 263 10 10, g32p_row17_traceSegment_069_0263_0010, g32p_row17_traceSegment_069_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 243 20 20, g32p_row17_traceSegment_069_0243_0020, g32p_row17_traceSegment_069_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 293 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 283 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 283 10 10, g32p_row17_traceSegment_069_0283_0010, g32p_row17_traceSegment_069_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 313 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 303 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 303 10 11, g32p_row17_traceSegment_069_0303_0010, g32p_row17_traceSegment_069_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 283 41 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 283 20 21, g32p_row17_traceSegment_069_0283_0020, g32p_row17_traceSegment_069_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 243 81 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 243 40 41, g32p_row17_traceSegment_069_0243_0040, g32p_row17_traceSegment_069_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_069 162 162 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 162 81 81, g32p_row17_traceSegment_069_0162_0081, g32p_row17_traceSegment_069_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_069 0 324 = [5, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 0 162 162, g32p_row17_traceSegment_069_0000_0162, g32p_row17_traceSegment_069_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 324 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 334 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 324 20 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 324 10 10, g32p_row17_traceSegment_069_0324_0010, g32p_row17_traceSegment_069_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 344 10 10, g32p_row17_traceSegment_069_0344_0010, g32p_row17_traceSegment_069_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 324 40 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 324 20 20, g32p_row17_traceSegment_069_0324_0020, g32p_row17_traceSegment_069_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 364 10 10, g32p_row17_traceSegment_069_0364_0010, g32p_row17_traceSegment_069_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 384 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 384 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 384 10 11, g32p_row17_traceSegment_069_0384_0010, g32p_row17_traceSegment_069_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 364 41 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 364 20 21, g32p_row17_traceSegment_069_0364_0020, g32p_row17_traceSegment_069_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 324 81 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 324 40 41, g32p_row17_traceSegment_069_0324_0040, g32p_row17_traceSegment_069_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 415 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 405 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 405 10 10, g32p_row17_traceSegment_069_0405_0010, g32p_row17_traceSegment_069_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 435 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 425 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 425 10 10, g32p_row17_traceSegment_069_0425_0010, g32p_row17_traceSegment_069_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 405 40 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 405 20 20, g32p_row17_traceSegment_069_0405_0020, g32p_row17_traceSegment_069_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 455 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 445 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 445 10 10, g32p_row17_traceSegment_069_0445_0010, g32p_row17_traceSegment_069_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 465 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 475 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 465 21 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 465 10 11, g32p_row17_traceSegment_069_0465_0010, g32p_row17_traceSegment_069_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 445 41 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 445 20 21, g32p_row17_traceSegment_069_0445_0020, g32p_row17_traceSegment_069_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 405 81 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 405 40 41, g32p_row17_traceSegment_069_0405_0040, g32p_row17_traceSegment_069_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_069 324 162 = [3, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 324 81 81, g32p_row17_traceSegment_069_0324_0081, g32p_row17_traceSegment_069_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 486 10 10, g32p_row17_traceSegment_069_0486_0010, g32p_row17_traceSegment_069_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 506 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 516 10 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 506 20 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 506 10 10, g32p_row17_traceSegment_069_0506_0010, g32p_row17_traceSegment_069_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 486 40 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 486 20 20, g32p_row17_traceSegment_069_0486_0020, g32p_row17_traceSegment_069_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 536 10 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 526 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 526 10 10, g32p_row17_traceSegment_069_0526_0010, g32p_row17_traceSegment_069_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 556 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 546 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 546 10 11, g32p_row17_traceSegment_069_0546_0010, g32p_row17_traceSegment_069_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 526 41 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 526 20 21, g32p_row17_traceSegment_069_0526_0020, g32p_row17_traceSegment_069_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 486 81 = [4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 486 40 41, g32p_row17_traceSegment_069_0486_0040, g32p_row17_traceSegment_069_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 567 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 567 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 567 10 10, g32p_row17_traceSegment_069_0567_0010, g32p_row17_traceSegment_069_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 597 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 587 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 587 10 10, g32p_row17_traceSegment_069_0587_0010, g32p_row17_traceSegment_069_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 567 40 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 567 20 20, g32p_row17_traceSegment_069_0567_0020, g32p_row17_traceSegment_069_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 607 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 617 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 607 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 607 10 10, g32p_row17_traceSegment_069_0607_0010, g32p_row17_traceSegment_069_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 627 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 627 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 627 10 11, g32p_row17_traceSegment_069_0627_0010, g32p_row17_traceSegment_069_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 607 41 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 607 20 21, g32p_row17_traceSegment_069_0607_0020, g32p_row17_traceSegment_069_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 567 81 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 567 40 41, g32p_row17_traceSegment_069_0567_0040, g32p_row17_traceSegment_069_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_069 486 162 = [4, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 486 81 81, g32p_row17_traceSegment_069_0486_0081, g32p_row17_traceSegment_069_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_069 324 324 = [7, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 324 162 162, g32p_row17_traceSegment_069_0324_0162, g32p_row17_traceSegment_069_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_069 0 648 = [12, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 0 324 324, g32p_row17_traceSegment_069_0000_0324, g32p_row17_traceSegment_069_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 648 10 10, g32p_row17_traceSegment_069_0648_0010, g32p_row17_traceSegment_069_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 668 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 668 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 668 10 10, g32p_row17_traceSegment_069_0668_0010, g32p_row17_traceSegment_069_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 648 40 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 648 20 20, g32p_row17_traceSegment_069_0648_0020, g32p_row17_traceSegment_069_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 688 10 10, g32p_row17_traceSegment_069_0688_0010, g32p_row17_traceSegment_069_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 708 10 11, g32p_row17_traceSegment_069_0708_0010, g32p_row17_traceSegment_069_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 688 20 21, g32p_row17_traceSegment_069_0688_0020, g32p_row17_traceSegment_069_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 648 81 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 648 40 41, g32p_row17_traceSegment_069_0648_0040, g32p_row17_traceSegment_069_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 729 10 10, g32p_row17_traceSegment_069_0729_0010, g32p_row17_traceSegment_069_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 749 10 10, g32p_row17_traceSegment_069_0749_0010, g32p_row17_traceSegment_069_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 729 20 20, g32p_row17_traceSegment_069_0729_0020, g32p_row17_traceSegment_069_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 779 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 769 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 769 10 10, g32p_row17_traceSegment_069_0769_0010, g32p_row17_traceSegment_069_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 789 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 789 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 789 10 11, g32p_row17_traceSegment_069_0789_0010, g32p_row17_traceSegment_069_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 769 41 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 769 20 21, g32p_row17_traceSegment_069_0769_0020, g32p_row17_traceSegment_069_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 729 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 729 40 41, g32p_row17_traceSegment_069_0729_0040, g32p_row17_traceSegment_069_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_069 648 162 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 648 81 81, g32p_row17_traceSegment_069_0648_0081, g32p_row17_traceSegment_069_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 820 10 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 810 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 810 10 10, g32p_row17_traceSegment_069_0810_0010, g32p_row17_traceSegment_069_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 830 10 10, g32p_row17_traceSegment_069_0830_0010, g32p_row17_traceSegment_069_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 810 40 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 810 20 20, g32p_row17_traceSegment_069_0810_0020, g32p_row17_traceSegment_069_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 860 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 850 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 850 10 10, g32p_row17_traceSegment_069_0850_0010, g32p_row17_traceSegment_069_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 870 10 11, g32p_row17_traceSegment_069_0870_0010, g32p_row17_traceSegment_069_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 850 41 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 850 20 21, g32p_row17_traceSegment_069_0850_0020, g32p_row17_traceSegment_069_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 810 81 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 810 40 41, g32p_row17_traceSegment_069_0810_0040, g32p_row17_traceSegment_069_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 891 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 891 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 891 10 10, g32p_row17_traceSegment_069_0891_0010, g32p_row17_traceSegment_069_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 921 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 911 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 911 10 10, g32p_row17_traceSegment_069_0911_0010, g32p_row17_traceSegment_069_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 891 40 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 891 20 20, g32p_row17_traceSegment_069_0891_0020, g32p_row17_traceSegment_069_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 941 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 931 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 931 10 10, g32p_row17_traceSegment_069_0931_0010, g32p_row17_traceSegment_069_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 961 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 951 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 951 10 11, g32p_row17_traceSegment_069_0951_0010, g32p_row17_traceSegment_069_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 931 41 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 931 20 21, g32p_row17_traceSegment_069_0931_0020, g32p_row17_traceSegment_069_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 891 81 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 891 40 41, g32p_row17_traceSegment_069_0891_0040, g32p_row17_traceSegment_069_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_069 810 162 = [2, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 810 81 81, g32p_row17_traceSegment_069_0810_0081, g32p_row17_traceSegment_069_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_069 648 324 = [4, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 648 162 162, g32p_row17_traceSegment_069_0648_0162, g32p_row17_traceSegment_069_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 972 10 10, g32p_row17_traceSegment_069_0972_0010, g32p_row17_traceSegment_069_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 992 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1002 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 992 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 992 10 10, g32p_row17_traceSegment_069_0992_0010, g32p_row17_traceSegment_069_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 972 40 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 972 20 20, g32p_row17_traceSegment_069_0972_0020, g32p_row17_traceSegment_069_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1012 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 1012 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1012 10 10, g32p_row17_traceSegment_069_1012_0010, g32p_row17_traceSegment_069_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 1042 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 1032 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1032 10 11, g32p_row17_traceSegment_069_1032_0010, g32p_row17_traceSegment_069_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 1012 41 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1012 20 21, g32p_row17_traceSegment_069_1012_0020, g32p_row17_traceSegment_069_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 972 81 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 972 40 41, g32p_row17_traceSegment_069_0972_0040, g32p_row17_traceSegment_069_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1053 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 1053 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1053 10 10, g32p_row17_traceSegment_069_1053_0010, g32p_row17_traceSegment_069_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1083 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 1073 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1073 10 10, g32p_row17_traceSegment_069_1073_0010, g32p_row17_traceSegment_069_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 1053 40 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1053 20 20, g32p_row17_traceSegment_069_1053_0020, g32p_row17_traceSegment_069_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1093 10 10, g32p_row17_traceSegment_069_1093_0010, g32p_row17_traceSegment_069_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1113 10 11, g32p_row17_traceSegment_069_1113_0010, g32p_row17_traceSegment_069_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1093 20 21, g32p_row17_traceSegment_069_1093_0020, g32p_row17_traceSegment_069_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 1053 81 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1053 40 41, g32p_row17_traceSegment_069_1053_0040, g32p_row17_traceSegment_069_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_069 972 162 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 972 81 81, g32p_row17_traceSegment_069_0972_0081, g32p_row17_traceSegment_069_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1134 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 1134 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1134 10 10, g32p_row17_traceSegment_069_1134_0010, g32p_row17_traceSegment_069_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1154 10 10, g32p_row17_traceSegment_069_1154_0010, g32p_row17_traceSegment_069_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 1134 40 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1134 20 20, g32p_row17_traceSegment_069_1134_0020, g32p_row17_traceSegment_069_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1174 10 10, g32p_row17_traceSegment_069_1174_0010, g32p_row17_traceSegment_069_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1194 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 1194 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1194 10 11, g32p_row17_traceSegment_069_1194_0010, g32p_row17_traceSegment_069_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 1174 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1174 20 21, g32p_row17_traceSegment_069_1174_0020, g32p_row17_traceSegment_069_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 1134 81 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1134 40 41, g32p_row17_traceSegment_069_1134_0040, g32p_row17_traceSegment_069_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1225 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 1215 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1215 10 10, g32p_row17_traceSegment_069_1215_0010, g32p_row17_traceSegment_069_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1235 10 10, g32p_row17_traceSegment_069_1235_0010, g32p_row17_traceSegment_069_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_069 1215 40 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1215 20 20, g32p_row17_traceSegment_069_1215_0020, g32p_row17_traceSegment_069_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1255 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1265 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_069 1255 20 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1255 10 10, g32p_row17_traceSegment_069_1255_0010, g32p_row17_traceSegment_069_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_069 1275 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_069 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_069_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_069 1275 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1275 10 11, g32p_row17_traceSegment_069_1275_0010, g32p_row17_traceSegment_069_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_069 1255 41 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1255 20 21, g32p_row17_traceSegment_069_1255_0020, g32p_row17_traceSegment_069_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_069 1215 81 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1215 40 41, g32p_row17_traceSegment_069_1215_0040, g32p_row17_traceSegment_069_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_069_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_069 1134 162 = [2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 1134 81 81, g32p_row17_traceSegment_069_1134_0081, g32p_row17_traceSegment_069_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_069 972 324 = [2, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 972 162 162, g32p_row17_traceSegment_069_0972_0162, g32p_row17_traceSegment_069_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_069 648 648 = [6, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 648 324 324, g32p_row17_traceSegment_069_0648_0324, g32p_row17_traceSegment_069_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_069_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_069 0 1296 = [18, 0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_069 0 648 648, g32p_row17_traceSegment_069_0000_0648, g32p_row17_traceSegment_069_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 69 = [18, 0, 0, 36] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_069_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_071 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 71 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_071_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 0 10 10, g32p_row17_traceSegment_071_0000_0010, g32p_row17_traceSegment_071_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 20 10 10, g32p_row17_traceSegment_071_0020_0010, g32p_row17_traceSegment_071_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 0 20 20, g32p_row17_traceSegment_071_0000_0020, g32p_row17_traceSegment_071_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 40 10 10, g32p_row17_traceSegment_071_0040_0010, g32p_row17_traceSegment_071_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 70 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 60 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 60 10 11, g32p_row17_traceSegment_071_0060_0010, g32p_row17_traceSegment_071_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 40 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 40 20 21, g32p_row17_traceSegment_071_0040_0020, g32p_row17_traceSegment_071_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 0 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 0 40 41, g32p_row17_traceSegment_071_0000_0040, g32p_row17_traceSegment_071_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 81 10 10, g32p_row17_traceSegment_071_0081_0010, g32p_row17_traceSegment_071_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 111 10 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 101 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 101 10 10, g32p_row17_traceSegment_071_0101_0010, g32p_row17_traceSegment_071_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 81 40 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 81 20 20, g32p_row17_traceSegment_071_0081_0020, g32p_row17_traceSegment_071_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 121 10 10, g32p_row17_traceSegment_071_0121_0010, g32p_row17_traceSegment_071_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 141 10 11, g32p_row17_traceSegment_071_0141_0010, g32p_row17_traceSegment_071_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 121 20 21, g32p_row17_traceSegment_071_0121_0020, g32p_row17_traceSegment_071_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 81 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 81 40 41, g32p_row17_traceSegment_071_0081_0040, g32p_row17_traceSegment_071_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_071 0 162 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 0 81 81, g32p_row17_traceSegment_071_0000_0081, g32p_row17_traceSegment_071_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 162 10 10, g32p_row17_traceSegment_071_0162_0010, g32p_row17_traceSegment_071_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 182 10 10, g32p_row17_traceSegment_071_0182_0010, g32p_row17_traceSegment_071_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 162 20 20, g32p_row17_traceSegment_071_0162_0020, g32p_row17_traceSegment_071_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 202 10 10, g32p_row17_traceSegment_071_0202_0010, g32p_row17_traceSegment_071_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 222 10 11, g32p_row17_traceSegment_071_0222_0010, g32p_row17_traceSegment_071_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 202 20 21, g32p_row17_traceSegment_071_0202_0020, g32p_row17_traceSegment_071_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 162 40 41, g32p_row17_traceSegment_071_0162_0040, g32p_row17_traceSegment_071_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 243 10 10, g32p_row17_traceSegment_071_0243_0010, g32p_row17_traceSegment_071_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 263 10 10, g32p_row17_traceSegment_071_0263_0010, g32p_row17_traceSegment_071_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 243 20 20, g32p_row17_traceSegment_071_0243_0020, g32p_row17_traceSegment_071_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 283 10 10, g32p_row17_traceSegment_071_0283_0010, g32p_row17_traceSegment_071_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 303 10 11, g32p_row17_traceSegment_071_0303_0010, g32p_row17_traceSegment_071_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 283 20 21, g32p_row17_traceSegment_071_0283_0020, g32p_row17_traceSegment_071_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 243 40 41, g32p_row17_traceSegment_071_0243_0040, g32p_row17_traceSegment_071_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_071 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 162 81 81, g32p_row17_traceSegment_071_0162_0081, g32p_row17_traceSegment_071_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_071 0 324 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 0 162 162, g32p_row17_traceSegment_071_0000_0162, g32p_row17_traceSegment_071_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 324 10 10, g32p_row17_traceSegment_071_0324_0010, g32p_row17_traceSegment_071_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 344 10 10, g32p_row17_traceSegment_071_0344_0010, g32p_row17_traceSegment_071_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 324 20 20, g32p_row17_traceSegment_071_0324_0020, g32p_row17_traceSegment_071_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 364 10 10, g32p_row17_traceSegment_071_0364_0010, g32p_row17_traceSegment_071_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 384 10 11, g32p_row17_traceSegment_071_0384_0010, g32p_row17_traceSegment_071_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 364 20 21, g32p_row17_traceSegment_071_0364_0020, g32p_row17_traceSegment_071_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 324 40 41, g32p_row17_traceSegment_071_0324_0040, g32p_row17_traceSegment_071_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 405 10 10, g32p_row17_traceSegment_071_0405_0010, g32p_row17_traceSegment_071_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 425 10 10, g32p_row17_traceSegment_071_0425_0010, g32p_row17_traceSegment_071_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 405 20 20, g32p_row17_traceSegment_071_0405_0020, g32p_row17_traceSegment_071_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 445 10 10, g32p_row17_traceSegment_071_0445_0010, g32p_row17_traceSegment_071_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 465 10 11, g32p_row17_traceSegment_071_0465_0010, g32p_row17_traceSegment_071_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 445 20 21, g32p_row17_traceSegment_071_0445_0020, g32p_row17_traceSegment_071_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 405 40 41, g32p_row17_traceSegment_071_0405_0040, g32p_row17_traceSegment_071_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_071 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 324 81 81, g32p_row17_traceSegment_071_0324_0081, g32p_row17_traceSegment_071_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 486 10 10, g32p_row17_traceSegment_071_0486_0010, g32p_row17_traceSegment_071_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 506 10 10, g32p_row17_traceSegment_071_0506_0010, g32p_row17_traceSegment_071_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 486 20 20, g32p_row17_traceSegment_071_0486_0020, g32p_row17_traceSegment_071_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 526 10 10, g32p_row17_traceSegment_071_0526_0010, g32p_row17_traceSegment_071_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 546 10 11, g32p_row17_traceSegment_071_0546_0010, g32p_row17_traceSegment_071_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 526 20 21, g32p_row17_traceSegment_071_0526_0020, g32p_row17_traceSegment_071_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 486 40 41, g32p_row17_traceSegment_071_0486_0040, g32p_row17_traceSegment_071_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 567 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 567 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 567 10 10, g32p_row17_traceSegment_071_0567_0010, g32p_row17_traceSegment_071_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 587 10 10, g32p_row17_traceSegment_071_0587_0010, g32p_row17_traceSegment_071_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 567 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 567 20 20, g32p_row17_traceSegment_071_0567_0020, g32p_row17_traceSegment_071_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 607 10 10, g32p_row17_traceSegment_071_0607_0010, g32p_row17_traceSegment_071_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 627 10 11, g32p_row17_traceSegment_071_0627_0010, g32p_row17_traceSegment_071_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 607 20 21, g32p_row17_traceSegment_071_0607_0020, g32p_row17_traceSegment_071_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 567 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 567 40 41, g32p_row17_traceSegment_071_0567_0040, g32p_row17_traceSegment_071_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_071 486 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 486 81 81, g32p_row17_traceSegment_071_0486_0081, g32p_row17_traceSegment_071_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_071 324 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 324 162 162, g32p_row17_traceSegment_071_0324_0162, g32p_row17_traceSegment_071_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_071 0 648 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 0 324 324, g32p_row17_traceSegment_071_0000_0324, g32p_row17_traceSegment_071_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 648 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 648 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 648 10 10, g32p_row17_traceSegment_071_0648_0010, g32p_row17_traceSegment_071_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 668 10 10, g32p_row17_traceSegment_071_0668_0010, g32p_row17_traceSegment_071_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 648 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 648 20 20, g32p_row17_traceSegment_071_0648_0020, g32p_row17_traceSegment_071_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 698 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 688 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 688 10 10, g32p_row17_traceSegment_071_0688_0010, g32p_row17_traceSegment_071_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 708 10 11, g32p_row17_traceSegment_071_0708_0010, g32p_row17_traceSegment_071_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 688 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 688 20 21, g32p_row17_traceSegment_071_0688_0020, g32p_row17_traceSegment_071_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 648 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 648 40 41, g32p_row17_traceSegment_071_0648_0040, g32p_row17_traceSegment_071_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 729 10 10, g32p_row17_traceSegment_071_0729_0010, g32p_row17_traceSegment_071_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 749 10 10, g32p_row17_traceSegment_071_0749_0010, g32p_row17_traceSegment_071_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 729 20 20, g32p_row17_traceSegment_071_0729_0020, g32p_row17_traceSegment_071_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 769 10 10, g32p_row17_traceSegment_071_0769_0010, g32p_row17_traceSegment_071_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 799 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 789 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 789 10 11, g32p_row17_traceSegment_071_0789_0010, g32p_row17_traceSegment_071_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 769 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 769 20 21, g32p_row17_traceSegment_071_0769_0020, g32p_row17_traceSegment_071_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 729 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 729 40 41, g32p_row17_traceSegment_071_0729_0040, g32p_row17_traceSegment_071_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_071 648 162 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 648 81 81, g32p_row17_traceSegment_071_0648_0081, g32p_row17_traceSegment_071_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 810 10 10, g32p_row17_traceSegment_071_0810_0010, g32p_row17_traceSegment_071_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 830 10 10, g32p_row17_traceSegment_071_0830_0010, g32p_row17_traceSegment_071_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 810 20 20, g32p_row17_traceSegment_071_0810_0020, g32p_row17_traceSegment_071_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 850 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 850 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 850 10 10, g32p_row17_traceSegment_071_0850_0010, g32p_row17_traceSegment_071_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 870 10 11, g32p_row17_traceSegment_071_0870_0010, g32p_row17_traceSegment_071_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 850 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 850 20 21, g32p_row17_traceSegment_071_0850_0020, g32p_row17_traceSegment_071_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 810 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 810 40 41, g32p_row17_traceSegment_071_0810_0040, g32p_row17_traceSegment_071_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 891 10 10, g32p_row17_traceSegment_071_0891_0010, g32p_row17_traceSegment_071_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 911 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 921 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 911 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 911 10 10, g32p_row17_traceSegment_071_0911_0010, g32p_row17_traceSegment_071_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 891 40 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 891 20 20, g32p_row17_traceSegment_071_0891_0020, g32p_row17_traceSegment_071_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 931 10 10, g32p_row17_traceSegment_071_0931_0010, g32p_row17_traceSegment_071_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 951 10 11, g32p_row17_traceSegment_071_0951_0010, g32p_row17_traceSegment_071_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 931 20 21, g32p_row17_traceSegment_071_0931_0020, g32p_row17_traceSegment_071_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 891 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 891 40 41, g32p_row17_traceSegment_071_0891_0040, g32p_row17_traceSegment_071_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_071 810 162 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 810 81 81, g32p_row17_traceSegment_071_0810_0081, g32p_row17_traceSegment_071_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_071 648 324 = [6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 648 162 162, g32p_row17_traceSegment_071_0648_0162, g32p_row17_traceSegment_071_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 972 10 10, g32p_row17_traceSegment_071_0972_0010, g32p_row17_traceSegment_071_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 992 10 10, g32p_row17_traceSegment_071_0992_0010, g32p_row17_traceSegment_071_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 972 20 20, g32p_row17_traceSegment_071_0972_0020, g32p_row17_traceSegment_071_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1012 10 10, g32p_row17_traceSegment_071_1012_0010, g32p_row17_traceSegment_071_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1032 10 11, g32p_row17_traceSegment_071_1032_0010, g32p_row17_traceSegment_071_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1012 20 21, g32p_row17_traceSegment_071_1012_0020, g32p_row17_traceSegment_071_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 972 40 41, g32p_row17_traceSegment_071_0972_0040, g32p_row17_traceSegment_071_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1053 10 10, g32p_row17_traceSegment_071_1053_0010, g32p_row17_traceSegment_071_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1073 10 10, g32p_row17_traceSegment_071_1073_0010, g32p_row17_traceSegment_071_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1053 20 20, g32p_row17_traceSegment_071_1053_0020, g32p_row17_traceSegment_071_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1093 10 10, g32p_row17_traceSegment_071_1093_0010, g32p_row17_traceSegment_071_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1113 10 11, g32p_row17_traceSegment_071_1113_0010, g32p_row17_traceSegment_071_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1093 20 21, g32p_row17_traceSegment_071_1093_0020, g32p_row17_traceSegment_071_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1053 40 41, g32p_row17_traceSegment_071_1053_0040, g32p_row17_traceSegment_071_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_071 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 972 81 81, g32p_row17_traceSegment_071_0972_0081, g32p_row17_traceSegment_071_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1134 10 10, g32p_row17_traceSegment_071_1134_0010, g32p_row17_traceSegment_071_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1164 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 1154 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1154 10 10, g32p_row17_traceSegment_071_1154_0010, g32p_row17_traceSegment_071_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 1134 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1134 20 20, g32p_row17_traceSegment_071_1134_0020, g32p_row17_traceSegment_071_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1174 10 10, g32p_row17_traceSegment_071_1174_0010, g32p_row17_traceSegment_071_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1194 10 11, g32p_row17_traceSegment_071_1194_0010, g32p_row17_traceSegment_071_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1174 20 21, g32p_row17_traceSegment_071_1174_0020, g32p_row17_traceSegment_071_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 1134 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1134 40 41, g32p_row17_traceSegment_071_1134_0040, g32p_row17_traceSegment_071_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1215 10 10, g32p_row17_traceSegment_071_1215_0010, g32p_row17_traceSegment_071_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1235 10 10, g32p_row17_traceSegment_071_1235_0010, g32p_row17_traceSegment_071_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_071 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1215 20 20, g32p_row17_traceSegment_071_1215_0020, g32p_row17_traceSegment_071_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1255 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_071 1255 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1255 10 10, g32p_row17_traceSegment_071_1255_0010, g32p_row17_traceSegment_071_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_071 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_071 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_071_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_071 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1275 10 11, g32p_row17_traceSegment_071_1275_0010, g32p_row17_traceSegment_071_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_071 1255 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1255 20 21, g32p_row17_traceSegment_071_1255_0020, g32p_row17_traceSegment_071_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_071 1215 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1215 40 41, g32p_row17_traceSegment_071_1215_0040, g32p_row17_traceSegment_071_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_071_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_071 1134 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 1134 81 81, g32p_row17_traceSegment_071_1134_0081, g32p_row17_traceSegment_071_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_071 972 324 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 972 162 162, g32p_row17_traceSegment_071_0972_0162, g32p_row17_traceSegment_071_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_071 648 648 = [8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 648 324 324, g32p_row17_traceSegment_071_0648_0324, g32p_row17_traceSegment_071_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_071_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_071 0 1296 = [12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_071 0 648 648, g32p_row17_traceSegment_071_0000_0648, g32p_row17_traceSegment_071_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_071 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 71 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_071_0000_1296

end HodgeLean.Foundations.Program

end
end
