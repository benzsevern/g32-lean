import HodgeLean.Foundations.Program.G32PropFourSixPacked0367
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0372

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_085 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 85 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_085_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 0 10 10, g32p_row17_traceSegment_085_0000_0010, g32p_row17_traceSegment_085_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 20 10 10, g32p_row17_traceSegment_085_0020_0010, g32p_row17_traceSegment_085_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 0 20 20, g32p_row17_traceSegment_085_0000_0020, g32p_row17_traceSegment_085_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 40 10 10, g32p_row17_traceSegment_085_0040_0010, g32p_row17_traceSegment_085_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 60 10 11, g32p_row17_traceSegment_085_0060_0010, g32p_row17_traceSegment_085_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 40 20 21, g32p_row17_traceSegment_085_0040_0020, g32p_row17_traceSegment_085_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 0 40 41, g32p_row17_traceSegment_085_0000_0040, g32p_row17_traceSegment_085_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 81 10 10, g32p_row17_traceSegment_085_0081_0010, g32p_row17_traceSegment_085_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 101 10 10, g32p_row17_traceSegment_085_0101_0010, g32p_row17_traceSegment_085_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 81 20 20, g32p_row17_traceSegment_085_0081_0020, g32p_row17_traceSegment_085_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 121 10 10, g32p_row17_traceSegment_085_0121_0010, g32p_row17_traceSegment_085_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 141 10 11, g32p_row17_traceSegment_085_0141_0010, g32p_row17_traceSegment_085_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 121 20 21, g32p_row17_traceSegment_085_0121_0020, g32p_row17_traceSegment_085_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 81 40 41, g32p_row17_traceSegment_085_0081_0040, g32p_row17_traceSegment_085_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_085 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 0 81 81, g32p_row17_traceSegment_085_0000_0081, g32p_row17_traceSegment_085_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 162 10 10, g32p_row17_traceSegment_085_0162_0010, g32p_row17_traceSegment_085_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 182 10 10, g32p_row17_traceSegment_085_0182_0010, g32p_row17_traceSegment_085_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 162 20 20, g32p_row17_traceSegment_085_0162_0020, g32p_row17_traceSegment_085_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 202 10 10, g32p_row17_traceSegment_085_0202_0010, g32p_row17_traceSegment_085_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 222 10 11, g32p_row17_traceSegment_085_0222_0010, g32p_row17_traceSegment_085_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 202 20 21, g32p_row17_traceSegment_085_0202_0020, g32p_row17_traceSegment_085_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 162 40 41, g32p_row17_traceSegment_085_0162_0040, g32p_row17_traceSegment_085_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 243 10 10, g32p_row17_traceSegment_085_0243_0010, g32p_row17_traceSegment_085_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 263 10 10, g32p_row17_traceSegment_085_0263_0010, g32p_row17_traceSegment_085_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 243 20 20, g32p_row17_traceSegment_085_0243_0020, g32p_row17_traceSegment_085_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 283 10 10, g32p_row17_traceSegment_085_0283_0010, g32p_row17_traceSegment_085_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 303 10 11, g32p_row17_traceSegment_085_0303_0010, g32p_row17_traceSegment_085_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 283 20 21, g32p_row17_traceSegment_085_0283_0020, g32p_row17_traceSegment_085_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 243 40 41, g32p_row17_traceSegment_085_0243_0040, g32p_row17_traceSegment_085_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_085 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 162 81 81, g32p_row17_traceSegment_085_0162_0081, g32p_row17_traceSegment_085_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_085 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 0 162 162, g32p_row17_traceSegment_085_0000_0162, g32p_row17_traceSegment_085_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 324 10 10, g32p_row17_traceSegment_085_0324_0010, g32p_row17_traceSegment_085_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 344 10 10, g32p_row17_traceSegment_085_0344_0010, g32p_row17_traceSegment_085_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 324 20 20, g32p_row17_traceSegment_085_0324_0020, g32p_row17_traceSegment_085_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 364 10 10, g32p_row17_traceSegment_085_0364_0010, g32p_row17_traceSegment_085_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 384 10 11, g32p_row17_traceSegment_085_0384_0010, g32p_row17_traceSegment_085_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 364 20 21, g32p_row17_traceSegment_085_0364_0020, g32p_row17_traceSegment_085_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 324 40 41, g32p_row17_traceSegment_085_0324_0040, g32p_row17_traceSegment_085_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 405 10 10, g32p_row17_traceSegment_085_0405_0010, g32p_row17_traceSegment_085_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 425 10 10, g32p_row17_traceSegment_085_0425_0010, g32p_row17_traceSegment_085_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 405 20 20, g32p_row17_traceSegment_085_0405_0020, g32p_row17_traceSegment_085_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 445 10 10, g32p_row17_traceSegment_085_0445_0010, g32p_row17_traceSegment_085_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 465 10 11, g32p_row17_traceSegment_085_0465_0010, g32p_row17_traceSegment_085_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 445 20 21, g32p_row17_traceSegment_085_0445_0020, g32p_row17_traceSegment_085_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 405 40 41, g32p_row17_traceSegment_085_0405_0040, g32p_row17_traceSegment_085_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_085 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 324 81 81, g32p_row17_traceSegment_085_0324_0081, g32p_row17_traceSegment_085_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 486 10 10, g32p_row17_traceSegment_085_0486_0010, g32p_row17_traceSegment_085_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 506 10 10, g32p_row17_traceSegment_085_0506_0010, g32p_row17_traceSegment_085_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 486 20 20, g32p_row17_traceSegment_085_0486_0020, g32p_row17_traceSegment_085_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 526 10 10, g32p_row17_traceSegment_085_0526_0010, g32p_row17_traceSegment_085_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 546 10 11, g32p_row17_traceSegment_085_0546_0010, g32p_row17_traceSegment_085_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 526 20 21, g32p_row17_traceSegment_085_0526_0020, g32p_row17_traceSegment_085_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 486 40 41, g32p_row17_traceSegment_085_0486_0040, g32p_row17_traceSegment_085_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 567 10 10, g32p_row17_traceSegment_085_0567_0010, g32p_row17_traceSegment_085_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 587 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 587 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 587 10 10, g32p_row17_traceSegment_085_0587_0010, g32p_row17_traceSegment_085_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 567 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 567 20 20, g32p_row17_traceSegment_085_0567_0020, g32p_row17_traceSegment_085_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 607 10 10, g32p_row17_traceSegment_085_0607_0010, g32p_row17_traceSegment_085_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 627 10 11, g32p_row17_traceSegment_085_0627_0010, g32p_row17_traceSegment_085_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 607 20 21, g32p_row17_traceSegment_085_0607_0020, g32p_row17_traceSegment_085_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 567 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 567 40 41, g32p_row17_traceSegment_085_0567_0040, g32p_row17_traceSegment_085_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_085 486 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 486 81 81, g32p_row17_traceSegment_085_0486_0081, g32p_row17_traceSegment_085_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_085 324 324 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 324 162 162, g32p_row17_traceSegment_085_0324_0162, g32p_row17_traceSegment_085_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_085 0 648 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 0 324 324, g32p_row17_traceSegment_085_0000_0324, g32p_row17_traceSegment_085_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 648 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 648 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 648 10 10, g32p_row17_traceSegment_085_0648_0010, g32p_row17_traceSegment_085_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 668 10 10, g32p_row17_traceSegment_085_0668_0010, g32p_row17_traceSegment_085_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 648 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 648 20 20, g32p_row17_traceSegment_085_0648_0020, g32p_row17_traceSegment_085_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 688 10 10, g32p_row17_traceSegment_085_0688_0010, g32p_row17_traceSegment_085_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 708 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 708 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 708 10 11, g32p_row17_traceSegment_085_0708_0010, g32p_row17_traceSegment_085_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 688 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 688 20 21, g32p_row17_traceSegment_085_0688_0020, g32p_row17_traceSegment_085_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 648 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 648 40 41, g32p_row17_traceSegment_085_0648_0040, g32p_row17_traceSegment_085_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 729 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 729 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 729 10 10, g32p_row17_traceSegment_085_0729_0010, g32p_row17_traceSegment_085_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 749 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 749 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 749 10 10, g32p_row17_traceSegment_085_0749_0010, g32p_row17_traceSegment_085_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 729 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 729 20 20, g32p_row17_traceSegment_085_0729_0020, g32p_row17_traceSegment_085_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 769 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 769 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 769 10 10, g32p_row17_traceSegment_085_0769_0010, g32p_row17_traceSegment_085_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 789 10 11, g32p_row17_traceSegment_085_0789_0010, g32p_row17_traceSegment_085_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 769 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 769 20 21, g32p_row17_traceSegment_085_0769_0020, g32p_row17_traceSegment_085_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 729 81 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 729 40 41, g32p_row17_traceSegment_085_0729_0040, g32p_row17_traceSegment_085_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_085 648 162 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 648 81 81, g32p_row17_traceSegment_085_0648_0081, g32p_row17_traceSegment_085_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 820 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 810 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 810 10 10, g32p_row17_traceSegment_085_0810_0010, g32p_row17_traceSegment_085_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 830 10 10, g32p_row17_traceSegment_085_0830_0010, g32p_row17_traceSegment_085_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 810 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 810 20 20, g32p_row17_traceSegment_085_0810_0020, g32p_row17_traceSegment_085_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 850 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 850 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 850 10 10, g32p_row17_traceSegment_085_0850_0010, g32p_row17_traceSegment_085_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 870 10 11, g32p_row17_traceSegment_085_0870_0010, g32p_row17_traceSegment_085_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 850 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 850 20 21, g32p_row17_traceSegment_085_0850_0020, g32p_row17_traceSegment_085_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 810 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 810 40 41, g32p_row17_traceSegment_085_0810_0040, g32p_row17_traceSegment_085_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 891 10 10, g32p_row17_traceSegment_085_0891_0010, g32p_row17_traceSegment_085_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 911 10 10, g32p_row17_traceSegment_085_0911_0010, g32p_row17_traceSegment_085_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 891 20 20, g32p_row17_traceSegment_085_0891_0020, g32p_row17_traceSegment_085_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 941 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 931 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 931 10 10, g32p_row17_traceSegment_085_0931_0010, g32p_row17_traceSegment_085_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 951 10 11, g32p_row17_traceSegment_085_0951_0010, g32p_row17_traceSegment_085_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 931 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 931 20 21, g32p_row17_traceSegment_085_0931_0020, g32p_row17_traceSegment_085_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 891 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 891 40 41, g32p_row17_traceSegment_085_0891_0040, g32p_row17_traceSegment_085_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_085 810 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 810 81 81, g32p_row17_traceSegment_085_0810_0081, g32p_row17_traceSegment_085_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_085 648 324 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 648 162 162, g32p_row17_traceSegment_085_0648_0162, g32p_row17_traceSegment_085_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 972 10 10, g32p_row17_traceSegment_085_0972_0010, g32p_row17_traceSegment_085_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 992 10 10, g32p_row17_traceSegment_085_0992_0010, g32p_row17_traceSegment_085_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 972 20 20, g32p_row17_traceSegment_085_0972_0020, g32p_row17_traceSegment_085_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1012 10 10, g32p_row17_traceSegment_085_1012_0010, g32p_row17_traceSegment_085_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1032 10 11, g32p_row17_traceSegment_085_1032_0010, g32p_row17_traceSegment_085_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1012 20 21, g32p_row17_traceSegment_085_1012_0020, g32p_row17_traceSegment_085_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 972 40 41, g32p_row17_traceSegment_085_0972_0040, g32p_row17_traceSegment_085_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1053 10 10, g32p_row17_traceSegment_085_1053_0010, g32p_row17_traceSegment_085_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1073 10 10, g32p_row17_traceSegment_085_1073_0010, g32p_row17_traceSegment_085_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1053 20 20, g32p_row17_traceSegment_085_1053_0020, g32p_row17_traceSegment_085_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1103 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 1093 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1093 10 10, g32p_row17_traceSegment_085_1093_0010, g32p_row17_traceSegment_085_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1113 10 11, g32p_row17_traceSegment_085_1113_0010, g32p_row17_traceSegment_085_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 1093 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1093 20 21, g32p_row17_traceSegment_085_1093_0020, g32p_row17_traceSegment_085_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 1053 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1053 40 41, g32p_row17_traceSegment_085_1053_0040, g32p_row17_traceSegment_085_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_085 972 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 972 81 81, g32p_row17_traceSegment_085_0972_0081, g32p_row17_traceSegment_085_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1134 10 10, g32p_row17_traceSegment_085_1134_0010, g32p_row17_traceSegment_085_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1154 10 10, g32p_row17_traceSegment_085_1154_0010, g32p_row17_traceSegment_085_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1134 20 20, g32p_row17_traceSegment_085_1134_0020, g32p_row17_traceSegment_085_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1184 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 1174 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1174 10 10, g32p_row17_traceSegment_085_1174_0010, g32p_row17_traceSegment_085_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1194 10 11, g32p_row17_traceSegment_085_1194_0010, g32p_row17_traceSegment_085_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 1174 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1174 20 21, g32p_row17_traceSegment_085_1174_0020, g32p_row17_traceSegment_085_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 1134 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1134 40 41, g32p_row17_traceSegment_085_1134_0040, g32p_row17_traceSegment_085_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1215 10 10, g32p_row17_traceSegment_085_1215_0010, g32p_row17_traceSegment_085_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1245 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 1235 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1235 10 10, g32p_row17_traceSegment_085_1235_0010, g32p_row17_traceSegment_085_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_085 1215 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1215 20 20, g32p_row17_traceSegment_085_1215_0020, g32p_row17_traceSegment_085_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_085 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1255 10 10, g32p_row17_traceSegment_085_1255_0010, g32p_row17_traceSegment_085_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_085 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_085 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_085_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_085 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1275 10 11, g32p_row17_traceSegment_085_1275_0010, g32p_row17_traceSegment_085_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_085 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1255 20 21, g32p_row17_traceSegment_085_1255_0020, g32p_row17_traceSegment_085_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_085 1215 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1215 40 41, g32p_row17_traceSegment_085_1215_0040, g32p_row17_traceSegment_085_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_085_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_085 1134 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 1134 81 81, g32p_row17_traceSegment_085_1134_0081, g32p_row17_traceSegment_085_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_085 972 324 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 972 162 162, g32p_row17_traceSegment_085_0972_0162, g32p_row17_traceSegment_085_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_085 648 648 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 648 324 324, g32p_row17_traceSegment_085_0648_0324, g32p_row17_traceSegment_085_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_085_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_085 0 1296 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_085 0 648 648, g32p_row17_traceSegment_085_0000_0648, g32p_row17_traceSegment_085_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_085 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 85 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_085_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_086 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 86 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_086_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 0 10 10, g32p_row17_traceSegment_086_0000_0010, g32p_row17_traceSegment_086_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 20 10 10, g32p_row17_traceSegment_086_0020_0010, g32p_row17_traceSegment_086_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 0 20 20, g32p_row17_traceSegment_086_0000_0020, g32p_row17_traceSegment_086_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 40 10 10, g32p_row17_traceSegment_086_0040_0010, g32p_row17_traceSegment_086_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 60 10 11, g32p_row17_traceSegment_086_0060_0010, g32p_row17_traceSegment_086_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 40 20 21, g32p_row17_traceSegment_086_0040_0020, g32p_row17_traceSegment_086_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 0 40 41, g32p_row17_traceSegment_086_0000_0040, g32p_row17_traceSegment_086_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 81 10 10, g32p_row17_traceSegment_086_0081_0010, g32p_row17_traceSegment_086_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 101 10 10, g32p_row17_traceSegment_086_0101_0010, g32p_row17_traceSegment_086_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 81 20 20, g32p_row17_traceSegment_086_0081_0020, g32p_row17_traceSegment_086_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 121 10 10, g32p_row17_traceSegment_086_0121_0010, g32p_row17_traceSegment_086_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 141 10 11, g32p_row17_traceSegment_086_0141_0010, g32p_row17_traceSegment_086_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 121 20 21, g32p_row17_traceSegment_086_0121_0020, g32p_row17_traceSegment_086_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 81 40 41, g32p_row17_traceSegment_086_0081_0040, g32p_row17_traceSegment_086_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_086 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 0 81 81, g32p_row17_traceSegment_086_0000_0081, g32p_row17_traceSegment_086_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 162 10 10, g32p_row17_traceSegment_086_0162_0010, g32p_row17_traceSegment_086_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 182 10 10, g32p_row17_traceSegment_086_0182_0010, g32p_row17_traceSegment_086_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 162 20 20, g32p_row17_traceSegment_086_0162_0020, g32p_row17_traceSegment_086_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 202 10 10, g32p_row17_traceSegment_086_0202_0010, g32p_row17_traceSegment_086_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 222 10 11, g32p_row17_traceSegment_086_0222_0010, g32p_row17_traceSegment_086_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 202 20 21, g32p_row17_traceSegment_086_0202_0020, g32p_row17_traceSegment_086_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 162 40 41, g32p_row17_traceSegment_086_0162_0040, g32p_row17_traceSegment_086_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 243 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 243 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 243 10 10, g32p_row17_traceSegment_086_0243_0010, g32p_row17_traceSegment_086_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 273 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 263 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 263 10 10, g32p_row17_traceSegment_086_0263_0010, g32p_row17_traceSegment_086_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 243 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 243 20 20, g32p_row17_traceSegment_086_0243_0020, g32p_row17_traceSegment_086_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 283 10 10, g32p_row17_traceSegment_086_0283_0010, g32p_row17_traceSegment_086_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 313 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 303 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 303 10 11, g32p_row17_traceSegment_086_0303_0010, g32p_row17_traceSegment_086_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 283 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 283 20 21, g32p_row17_traceSegment_086_0283_0020, g32p_row17_traceSegment_086_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 243 81 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 243 40 41, g32p_row17_traceSegment_086_0243_0040, g32p_row17_traceSegment_086_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_086 162 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 162 81 81, g32p_row17_traceSegment_086_0162_0081, g32p_row17_traceSegment_086_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_086 0 324 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 0 162 162, g32p_row17_traceSegment_086_0000_0162, g32p_row17_traceSegment_086_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 324 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 334 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 324 20 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 324 10 10, g32p_row17_traceSegment_086_0324_0010, g32p_row17_traceSegment_086_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 344 10 10, g32p_row17_traceSegment_086_0344_0010, g32p_row17_traceSegment_086_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 324 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 324 20 20, g32p_row17_traceSegment_086_0324_0020, g32p_row17_traceSegment_086_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 364 10 10, g32p_row17_traceSegment_086_0364_0010, g32p_row17_traceSegment_086_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 384 10 11, g32p_row17_traceSegment_086_0384_0010, g32p_row17_traceSegment_086_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 364 20 21, g32p_row17_traceSegment_086_0364_0020, g32p_row17_traceSegment_086_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 324 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 324 40 41, g32p_row17_traceSegment_086_0324_0040, g32p_row17_traceSegment_086_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 405 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 405 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 405 10 10, g32p_row17_traceSegment_086_0405_0010, g32p_row17_traceSegment_086_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 425 10 10, g32p_row17_traceSegment_086_0425_0010, g32p_row17_traceSegment_086_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 405 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 405 20 20, g32p_row17_traceSegment_086_0405_0020, g32p_row17_traceSegment_086_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 445 10 10, g32p_row17_traceSegment_086_0445_0010, g32p_row17_traceSegment_086_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 465 10 11, g32p_row17_traceSegment_086_0465_0010, g32p_row17_traceSegment_086_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 445 20 21, g32p_row17_traceSegment_086_0445_0020, g32p_row17_traceSegment_086_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 405 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 405 40 41, g32p_row17_traceSegment_086_0405_0040, g32p_row17_traceSegment_086_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_086 324 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 324 81 81, g32p_row17_traceSegment_086_0324_0081, g32p_row17_traceSegment_086_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 486 10 10, g32p_row17_traceSegment_086_0486_0010, g32p_row17_traceSegment_086_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 506 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 506 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 506 10 10, g32p_row17_traceSegment_086_0506_0010, g32p_row17_traceSegment_086_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 486 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 486 20 20, g32p_row17_traceSegment_086_0486_0020, g32p_row17_traceSegment_086_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 526 10 10, g32p_row17_traceSegment_086_0526_0010, g32p_row17_traceSegment_086_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 546 10 11, g32p_row17_traceSegment_086_0546_0010, g32p_row17_traceSegment_086_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 526 20 21, g32p_row17_traceSegment_086_0526_0020, g32p_row17_traceSegment_086_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 486 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 486 40 41, g32p_row17_traceSegment_086_0486_0040, g32p_row17_traceSegment_086_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 567 10 10, g32p_row17_traceSegment_086_0567_0010, g32p_row17_traceSegment_086_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 587 10 10, g32p_row17_traceSegment_086_0587_0010, g32p_row17_traceSegment_086_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 567 20 20, g32p_row17_traceSegment_086_0567_0020, g32p_row17_traceSegment_086_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 607 10 10, g32p_row17_traceSegment_086_0607_0010, g32p_row17_traceSegment_086_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 627 10 11, g32p_row17_traceSegment_086_0627_0010, g32p_row17_traceSegment_086_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 607 20 21, g32p_row17_traceSegment_086_0607_0020, g32p_row17_traceSegment_086_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 567 40 41, g32p_row17_traceSegment_086_0567_0040, g32p_row17_traceSegment_086_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_086 486 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 486 81 81, g32p_row17_traceSegment_086_0486_0081, g32p_row17_traceSegment_086_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_086 324 324 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 324 162 162, g32p_row17_traceSegment_086_0324_0162, g32p_row17_traceSegment_086_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_086 0 648 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 0 324 324, g32p_row17_traceSegment_086_0000_0324, g32p_row17_traceSegment_086_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 648 10 10, g32p_row17_traceSegment_086_0648_0010, g32p_row17_traceSegment_086_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 668 10 10, g32p_row17_traceSegment_086_0668_0010, g32p_row17_traceSegment_086_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 648 20 20, g32p_row17_traceSegment_086_0648_0020, g32p_row17_traceSegment_086_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 688 10 10, g32p_row17_traceSegment_086_0688_0010, g32p_row17_traceSegment_086_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 708 10 11, g32p_row17_traceSegment_086_0708_0010, g32p_row17_traceSegment_086_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 688 20 21, g32p_row17_traceSegment_086_0688_0020, g32p_row17_traceSegment_086_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 648 40 41, g32p_row17_traceSegment_086_0648_0040, g32p_row17_traceSegment_086_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 729 10 10, g32p_row17_traceSegment_086_0729_0010, g32p_row17_traceSegment_086_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 749 10 10, g32p_row17_traceSegment_086_0749_0010, g32p_row17_traceSegment_086_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 729 20 20, g32p_row17_traceSegment_086_0729_0020, g32p_row17_traceSegment_086_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 769 10 10, g32p_row17_traceSegment_086_0769_0010, g32p_row17_traceSegment_086_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 789 10 11, g32p_row17_traceSegment_086_0789_0010, g32p_row17_traceSegment_086_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 769 20 21, g32p_row17_traceSegment_086_0769_0020, g32p_row17_traceSegment_086_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 729 40 41, g32p_row17_traceSegment_086_0729_0040, g32p_row17_traceSegment_086_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_086 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 648 81 81, g32p_row17_traceSegment_086_0648_0081, g32p_row17_traceSegment_086_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 810 10 10, g32p_row17_traceSegment_086_0810_0010, g32p_row17_traceSegment_086_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 830 10 10, g32p_row17_traceSegment_086_0830_0010, g32p_row17_traceSegment_086_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 810 20 20, g32p_row17_traceSegment_086_0810_0020, g32p_row17_traceSegment_086_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 850 10 10, g32p_row17_traceSegment_086_0850_0010, g32p_row17_traceSegment_086_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 870 10 11, g32p_row17_traceSegment_086_0870_0010, g32p_row17_traceSegment_086_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 850 20 21, g32p_row17_traceSegment_086_0850_0020, g32p_row17_traceSegment_086_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 810 40 41, g32p_row17_traceSegment_086_0810_0040, g32p_row17_traceSegment_086_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 891 10 10, g32p_row17_traceSegment_086_0891_0010, g32p_row17_traceSegment_086_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 911 10 10, g32p_row17_traceSegment_086_0911_0010, g32p_row17_traceSegment_086_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 891 20 20, g32p_row17_traceSegment_086_0891_0020, g32p_row17_traceSegment_086_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 931 10 10, g32p_row17_traceSegment_086_0931_0010, g32p_row17_traceSegment_086_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 951 10 11, g32p_row17_traceSegment_086_0951_0010, g32p_row17_traceSegment_086_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 931 20 21, g32p_row17_traceSegment_086_0931_0020, g32p_row17_traceSegment_086_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 891 40 41, g32p_row17_traceSegment_086_0891_0040, g32p_row17_traceSegment_086_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_086 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 810 81 81, g32p_row17_traceSegment_086_0810_0081, g32p_row17_traceSegment_086_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_086 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 648 162 162, g32p_row17_traceSegment_086_0648_0162, g32p_row17_traceSegment_086_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 972 10 10, g32p_row17_traceSegment_086_0972_0010, g32p_row17_traceSegment_086_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 992 10 10, g32p_row17_traceSegment_086_0992_0010, g32p_row17_traceSegment_086_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 972 20 20, g32p_row17_traceSegment_086_0972_0020, g32p_row17_traceSegment_086_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1012 10 10, g32p_row17_traceSegment_086_1012_0010, g32p_row17_traceSegment_086_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 1042 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 1032 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1032 10 11, g32p_row17_traceSegment_086_1032_0010, g32p_row17_traceSegment_086_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 1012 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1012 20 21, g32p_row17_traceSegment_086_1012_0020, g32p_row17_traceSegment_086_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 972 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 972 40 41, g32p_row17_traceSegment_086_0972_0040, g32p_row17_traceSegment_086_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1053 10 10, g32p_row17_traceSegment_086_1053_0010, g32p_row17_traceSegment_086_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1083 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 1073 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1073 10 10, g32p_row17_traceSegment_086_1073_0010, g32p_row17_traceSegment_086_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 1053 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1053 20 20, g32p_row17_traceSegment_086_1053_0020, g32p_row17_traceSegment_086_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1093 10 10, g32p_row17_traceSegment_086_1093_0010, g32p_row17_traceSegment_086_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1113 10 11, g32p_row17_traceSegment_086_1113_0010, g32p_row17_traceSegment_086_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1093 20 21, g32p_row17_traceSegment_086_1093_0020, g32p_row17_traceSegment_086_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 1053 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1053 40 41, g32p_row17_traceSegment_086_1053_0040, g32p_row17_traceSegment_086_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_086 972 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 972 81 81, g32p_row17_traceSegment_086_0972_0081, g32p_row17_traceSegment_086_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1134 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 1134 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1134 10 10, g32p_row17_traceSegment_086_1134_0010, g32p_row17_traceSegment_086_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1154 10 10, g32p_row17_traceSegment_086_1154_0010, g32p_row17_traceSegment_086_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 1134 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1134 20 20, g32p_row17_traceSegment_086_1134_0020, g32p_row17_traceSegment_086_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1174 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 1174 20 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1174 10 10, g32p_row17_traceSegment_086_1174_0010, g32p_row17_traceSegment_086_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1194 10 11, g32p_row17_traceSegment_086_1194_0010, g32p_row17_traceSegment_086_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 1174 41 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1174 20 21, g32p_row17_traceSegment_086_1174_0020, g32p_row17_traceSegment_086_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 1134 81 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1134 40 41, g32p_row17_traceSegment_086_1134_0040, g32p_row17_traceSegment_086_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1215 10 10, g32p_row17_traceSegment_086_1215_0010, g32p_row17_traceSegment_086_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1235 10 10, g32p_row17_traceSegment_086_1235_0010, g32p_row17_traceSegment_086_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_086 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1215 20 20, g32p_row17_traceSegment_086_1215_0020, g32p_row17_traceSegment_086_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_086 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1255 10 10, g32p_row17_traceSegment_086_1255_0010, g32p_row17_traceSegment_086_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_086 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_086 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_086_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_086 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1275 10 11, g32p_row17_traceSegment_086_1275_0010, g32p_row17_traceSegment_086_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_086 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1255 20 21, g32p_row17_traceSegment_086_1255_0020, g32p_row17_traceSegment_086_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_086 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1215 40 41, g32p_row17_traceSegment_086_1215_0040, g32p_row17_traceSegment_086_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_086_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_086 1134 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 1134 81 81, g32p_row17_traceSegment_086_1134_0081, g32p_row17_traceSegment_086_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_086 972 324 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 972 162 162, g32p_row17_traceSegment_086_0972_0162, g32p_row17_traceSegment_086_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_086 648 648 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 648 324 324, g32p_row17_traceSegment_086_0648_0324, g32p_row17_traceSegment_086_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_086_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_086 0 1296 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_086 0 648 648, g32p_row17_traceSegment_086_0000_0648, g32p_row17_traceSegment_086_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_086 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 86 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_086_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_087 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 87 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_087_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 0 10 10, g32p_row17_traceSegment_087_0000_0010, g32p_row17_traceSegment_087_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 20 10 10, g32p_row17_traceSegment_087_0020_0010, g32p_row17_traceSegment_087_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 0 20 20, g32p_row17_traceSegment_087_0000_0020, g32p_row17_traceSegment_087_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 40 10 10, g32p_row17_traceSegment_087_0040_0010, g32p_row17_traceSegment_087_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 60 10 11, g32p_row17_traceSegment_087_0060_0010, g32p_row17_traceSegment_087_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 40 20 21, g32p_row17_traceSegment_087_0040_0020, g32p_row17_traceSegment_087_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 0 40 41, g32p_row17_traceSegment_087_0000_0040, g32p_row17_traceSegment_087_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 81 10 10, g32p_row17_traceSegment_087_0081_0010, g32p_row17_traceSegment_087_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 101 10 10, g32p_row17_traceSegment_087_0101_0010, g32p_row17_traceSegment_087_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 81 20 20, g32p_row17_traceSegment_087_0081_0020, g32p_row17_traceSegment_087_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 121 10 10, g32p_row17_traceSegment_087_0121_0010, g32p_row17_traceSegment_087_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 141 10 11, g32p_row17_traceSegment_087_0141_0010, g32p_row17_traceSegment_087_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 121 20 21, g32p_row17_traceSegment_087_0121_0020, g32p_row17_traceSegment_087_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 81 40 41, g32p_row17_traceSegment_087_0081_0040, g32p_row17_traceSegment_087_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_087 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 0 81 81, g32p_row17_traceSegment_087_0000_0081, g32p_row17_traceSegment_087_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 162 10 10, g32p_row17_traceSegment_087_0162_0010, g32p_row17_traceSegment_087_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 182 10 10, g32p_row17_traceSegment_087_0182_0010, g32p_row17_traceSegment_087_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 162 20 20, g32p_row17_traceSegment_087_0162_0020, g32p_row17_traceSegment_087_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 202 10 10, g32p_row17_traceSegment_087_0202_0010, g32p_row17_traceSegment_087_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 222 10 11, g32p_row17_traceSegment_087_0222_0010, g32p_row17_traceSegment_087_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 202 20 21, g32p_row17_traceSegment_087_0202_0020, g32p_row17_traceSegment_087_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 162 40 41, g32p_row17_traceSegment_087_0162_0040, g32p_row17_traceSegment_087_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 243 10 10, g32p_row17_traceSegment_087_0243_0010, g32p_row17_traceSegment_087_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 263 10 10, g32p_row17_traceSegment_087_0263_0010, g32p_row17_traceSegment_087_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 243 20 20, g32p_row17_traceSegment_087_0243_0020, g32p_row17_traceSegment_087_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 283 10 10, g32p_row17_traceSegment_087_0283_0010, g32p_row17_traceSegment_087_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 303 10 11, g32p_row17_traceSegment_087_0303_0010, g32p_row17_traceSegment_087_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 283 20 21, g32p_row17_traceSegment_087_0283_0020, g32p_row17_traceSegment_087_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 243 40 41, g32p_row17_traceSegment_087_0243_0040, g32p_row17_traceSegment_087_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_087 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 162 81 81, g32p_row17_traceSegment_087_0162_0081, g32p_row17_traceSegment_087_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_087 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 0 162 162, g32p_row17_traceSegment_087_0000_0162, g32p_row17_traceSegment_087_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 324 10 10, g32p_row17_traceSegment_087_0324_0010, g32p_row17_traceSegment_087_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 344 10 10, g32p_row17_traceSegment_087_0344_0010, g32p_row17_traceSegment_087_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 324 20 20, g32p_row17_traceSegment_087_0324_0020, g32p_row17_traceSegment_087_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 364 10 10, g32p_row17_traceSegment_087_0364_0010, g32p_row17_traceSegment_087_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 384 10 11, g32p_row17_traceSegment_087_0384_0010, g32p_row17_traceSegment_087_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 364 20 21, g32p_row17_traceSegment_087_0364_0020, g32p_row17_traceSegment_087_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 324 40 41, g32p_row17_traceSegment_087_0324_0040, g32p_row17_traceSegment_087_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 405 10 10, g32p_row17_traceSegment_087_0405_0010, g32p_row17_traceSegment_087_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 425 10 10, g32p_row17_traceSegment_087_0425_0010, g32p_row17_traceSegment_087_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 405 20 20, g32p_row17_traceSegment_087_0405_0020, g32p_row17_traceSegment_087_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 445 10 10, g32p_row17_traceSegment_087_0445_0010, g32p_row17_traceSegment_087_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 465 10 11, g32p_row17_traceSegment_087_0465_0010, g32p_row17_traceSegment_087_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 445 20 21, g32p_row17_traceSegment_087_0445_0020, g32p_row17_traceSegment_087_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 405 40 41, g32p_row17_traceSegment_087_0405_0040, g32p_row17_traceSegment_087_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_087 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 324 81 81, g32p_row17_traceSegment_087_0324_0081, g32p_row17_traceSegment_087_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 486 10 10, g32p_row17_traceSegment_087_0486_0010, g32p_row17_traceSegment_087_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 506 10 10, g32p_row17_traceSegment_087_0506_0010, g32p_row17_traceSegment_087_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 486 20 20, g32p_row17_traceSegment_087_0486_0020, g32p_row17_traceSegment_087_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 526 10 10, g32p_row17_traceSegment_087_0526_0010, g32p_row17_traceSegment_087_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 546 10 11, g32p_row17_traceSegment_087_0546_0010, g32p_row17_traceSegment_087_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 526 20 21, g32p_row17_traceSegment_087_0526_0020, g32p_row17_traceSegment_087_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 486 40 41, g32p_row17_traceSegment_087_0486_0040, g32p_row17_traceSegment_087_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 567 10 10, g32p_row17_traceSegment_087_0567_0010, g32p_row17_traceSegment_087_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 587 10 10, g32p_row17_traceSegment_087_0587_0010, g32p_row17_traceSegment_087_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 567 20 20, g32p_row17_traceSegment_087_0567_0020, g32p_row17_traceSegment_087_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 607 10 10, g32p_row17_traceSegment_087_0607_0010, g32p_row17_traceSegment_087_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 627 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 627 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 627 10 11, g32p_row17_traceSegment_087_0627_0010, g32p_row17_traceSegment_087_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 607 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 607 20 21, g32p_row17_traceSegment_087_0607_0020, g32p_row17_traceSegment_087_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 567 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 567 40 41, g32p_row17_traceSegment_087_0567_0040, g32p_row17_traceSegment_087_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_087 486 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 486 81 81, g32p_row17_traceSegment_087_0486_0081, g32p_row17_traceSegment_087_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_087 324 324 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 324 162 162, g32p_row17_traceSegment_087_0324_0162, g32p_row17_traceSegment_087_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_087 0 648 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 0 324 324, g32p_row17_traceSegment_087_0000_0324, g32p_row17_traceSegment_087_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 648 10 10, g32p_row17_traceSegment_087_0648_0010, g32p_row17_traceSegment_087_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 668 10 10, g32p_row17_traceSegment_087_0668_0010, g32p_row17_traceSegment_087_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 648 20 20, g32p_row17_traceSegment_087_0648_0020, g32p_row17_traceSegment_087_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 688 10 10, g32p_row17_traceSegment_087_0688_0010, g32p_row17_traceSegment_087_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 708 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 708 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 708 10 11, g32p_row17_traceSegment_087_0708_0010, g32p_row17_traceSegment_087_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 688 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 688 20 21, g32p_row17_traceSegment_087_0688_0020, g32p_row17_traceSegment_087_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 648 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 648 40 41, g32p_row17_traceSegment_087_0648_0040, g32p_row17_traceSegment_087_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 729 10 10, g32p_row17_traceSegment_087_0729_0010, g32p_row17_traceSegment_087_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 749 10 10, g32p_row17_traceSegment_087_0749_0010, g32p_row17_traceSegment_087_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 729 20 20, g32p_row17_traceSegment_087_0729_0020, g32p_row17_traceSegment_087_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 769 10 10, g32p_row17_traceSegment_087_0769_0010, g32p_row17_traceSegment_087_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 789 10 11, g32p_row17_traceSegment_087_0789_0010, g32p_row17_traceSegment_087_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 769 20 21, g32p_row17_traceSegment_087_0769_0020, g32p_row17_traceSegment_087_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 729 40 41, g32p_row17_traceSegment_087_0729_0040, g32p_row17_traceSegment_087_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_087 648 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 648 81 81, g32p_row17_traceSegment_087_0648_0081, g32p_row17_traceSegment_087_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 810 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 810 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 810 10 10, g32p_row17_traceSegment_087_0810_0010, g32p_row17_traceSegment_087_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 830 10 10, g32p_row17_traceSegment_087_0830_0010, g32p_row17_traceSegment_087_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 810 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 810 20 20, g32p_row17_traceSegment_087_0810_0020, g32p_row17_traceSegment_087_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 850 10 10, g32p_row17_traceSegment_087_0850_0010, g32p_row17_traceSegment_087_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 870 10 11, g32p_row17_traceSegment_087_0870_0010, g32p_row17_traceSegment_087_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 850 20 21, g32p_row17_traceSegment_087_0850_0020, g32p_row17_traceSegment_087_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 810 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 810 40 41, g32p_row17_traceSegment_087_0810_0040, g32p_row17_traceSegment_087_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 891 10 10, g32p_row17_traceSegment_087_0891_0010, g32p_row17_traceSegment_087_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 911 10 10, g32p_row17_traceSegment_087_0911_0010, g32p_row17_traceSegment_087_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 891 20 20, g32p_row17_traceSegment_087_0891_0020, g32p_row17_traceSegment_087_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 931 10 10, g32p_row17_traceSegment_087_0931_0010, g32p_row17_traceSegment_087_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 951 10 11, g32p_row17_traceSegment_087_0951_0010, g32p_row17_traceSegment_087_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 931 20 21, g32p_row17_traceSegment_087_0931_0020, g32p_row17_traceSegment_087_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 891 40 41, g32p_row17_traceSegment_087_0891_0040, g32p_row17_traceSegment_087_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_087 810 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 810 81 81, g32p_row17_traceSegment_087_0810_0081, g32p_row17_traceSegment_087_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_087 648 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 648 162 162, g32p_row17_traceSegment_087_0648_0162, g32p_row17_traceSegment_087_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 972 10 10, g32p_row17_traceSegment_087_0972_0010, g32p_row17_traceSegment_087_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 992 10 10, g32p_row17_traceSegment_087_0992_0010, g32p_row17_traceSegment_087_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 972 20 20, g32p_row17_traceSegment_087_0972_0020, g32p_row17_traceSegment_087_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1012 10 10, g32p_row17_traceSegment_087_1012_0010, g32p_row17_traceSegment_087_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1032 10 11, g32p_row17_traceSegment_087_1032_0010, g32p_row17_traceSegment_087_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1012 20 21, g32p_row17_traceSegment_087_1012_0020, g32p_row17_traceSegment_087_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 972 40 41, g32p_row17_traceSegment_087_0972_0040, g32p_row17_traceSegment_087_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1053 10 10, g32p_row17_traceSegment_087_1053_0010, g32p_row17_traceSegment_087_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1083 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 1073 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1073 10 10, g32p_row17_traceSegment_087_1073_0010, g32p_row17_traceSegment_087_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 1053 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1053 20 20, g32p_row17_traceSegment_087_1053_0020, g32p_row17_traceSegment_087_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1093 10 10, g32p_row17_traceSegment_087_1093_0010, g32p_row17_traceSegment_087_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1113 10 11, g32p_row17_traceSegment_087_1113_0010, g32p_row17_traceSegment_087_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1093 20 21, g32p_row17_traceSegment_087_1093_0020, g32p_row17_traceSegment_087_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 1053 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1053 40 41, g32p_row17_traceSegment_087_1053_0040, g32p_row17_traceSegment_087_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_087 972 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 972 81 81, g32p_row17_traceSegment_087_0972_0081, g32p_row17_traceSegment_087_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1134 10 10, g32p_row17_traceSegment_087_1134_0010, g32p_row17_traceSegment_087_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1154 10 10, g32p_row17_traceSegment_087_1154_0010, g32p_row17_traceSegment_087_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1134 20 20, g32p_row17_traceSegment_087_1134_0020, g32p_row17_traceSegment_087_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1174 10 10, g32p_row17_traceSegment_087_1174_0010, g32p_row17_traceSegment_087_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1194 10 11, g32p_row17_traceSegment_087_1194_0010, g32p_row17_traceSegment_087_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1174 20 21, g32p_row17_traceSegment_087_1174_0020, g32p_row17_traceSegment_087_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1134 40 41, g32p_row17_traceSegment_087_1134_0040, g32p_row17_traceSegment_087_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1215 10 10, g32p_row17_traceSegment_087_1215_0010, g32p_row17_traceSegment_087_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1235 10 10, g32p_row17_traceSegment_087_1235_0010, g32p_row17_traceSegment_087_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_087 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1215 20 20, g32p_row17_traceSegment_087_1215_0020, g32p_row17_traceSegment_087_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_087 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1255 10 10, g32p_row17_traceSegment_087_1255_0010, g32p_row17_traceSegment_087_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_087 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_087 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_087_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_087 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1275 10 11, g32p_row17_traceSegment_087_1275_0010, g32p_row17_traceSegment_087_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_087 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1255 20 21, g32p_row17_traceSegment_087_1255_0020, g32p_row17_traceSegment_087_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_087 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1215 40 41, g32p_row17_traceSegment_087_1215_0040, g32p_row17_traceSegment_087_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_087_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_087 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 1134 81 81, g32p_row17_traceSegment_087_1134_0081, g32p_row17_traceSegment_087_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_087 972 324 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 972 162 162, g32p_row17_traceSegment_087_0972_0162, g32p_row17_traceSegment_087_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_087 648 648 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 648 324 324, g32p_row17_traceSegment_087_0648_0324, g32p_row17_traceSegment_087_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_087_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_087 0 1296 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_087 0 648 648, g32p_row17_traceSegment_087_0000_0648, g32p_row17_traceSegment_087_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 87 = [0, 0, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_087_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_088 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 88 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_088_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 0 10 10, g32p_row17_traceSegment_088_0000_0010, g32p_row17_traceSegment_088_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 20 10 10, g32p_row17_traceSegment_088_0020_0010, g32p_row17_traceSegment_088_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 0 20 20, g32p_row17_traceSegment_088_0000_0020, g32p_row17_traceSegment_088_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 40 10 10, g32p_row17_traceSegment_088_0040_0010, g32p_row17_traceSegment_088_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 60 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 60 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 60 10 11, g32p_row17_traceSegment_088_0060_0010, g32p_row17_traceSegment_088_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 40 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 40 20 21, g32p_row17_traceSegment_088_0040_0020, g32p_row17_traceSegment_088_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 0 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 0 40 41, g32p_row17_traceSegment_088_0000_0040, g32p_row17_traceSegment_088_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 81 10 10, g32p_row17_traceSegment_088_0081_0010, g32p_row17_traceSegment_088_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 101 10 10, g32p_row17_traceSegment_088_0101_0010, g32p_row17_traceSegment_088_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 81 20 20, g32p_row17_traceSegment_088_0081_0020, g32p_row17_traceSegment_088_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 121 10 10, g32p_row17_traceSegment_088_0121_0010, g32p_row17_traceSegment_088_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 141 10 11, g32p_row17_traceSegment_088_0141_0010, g32p_row17_traceSegment_088_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 121 20 21, g32p_row17_traceSegment_088_0121_0020, g32p_row17_traceSegment_088_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 81 40 41, g32p_row17_traceSegment_088_0081_0040, g32p_row17_traceSegment_088_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_088 0 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 0 81 81, g32p_row17_traceSegment_088_0000_0081, g32p_row17_traceSegment_088_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 162 10 10, g32p_row17_traceSegment_088_0162_0010, g32p_row17_traceSegment_088_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 182 10 10, g32p_row17_traceSegment_088_0182_0010, g32p_row17_traceSegment_088_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 162 20 20, g32p_row17_traceSegment_088_0162_0020, g32p_row17_traceSegment_088_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 202 10 10, g32p_row17_traceSegment_088_0202_0010, g32p_row17_traceSegment_088_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 222 10 11, g32p_row17_traceSegment_088_0222_0010, g32p_row17_traceSegment_088_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 202 20 21, g32p_row17_traceSegment_088_0202_0020, g32p_row17_traceSegment_088_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 162 40 41, g32p_row17_traceSegment_088_0162_0040, g32p_row17_traceSegment_088_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 243 10 10, g32p_row17_traceSegment_088_0243_0010, g32p_row17_traceSegment_088_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 263 10 10, g32p_row17_traceSegment_088_0263_0010, g32p_row17_traceSegment_088_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 243 20 20, g32p_row17_traceSegment_088_0243_0020, g32p_row17_traceSegment_088_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 283 10 10, g32p_row17_traceSegment_088_0283_0010, g32p_row17_traceSegment_088_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 303 10 11, g32p_row17_traceSegment_088_0303_0010, g32p_row17_traceSegment_088_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 283 20 21, g32p_row17_traceSegment_088_0283_0020, g32p_row17_traceSegment_088_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 243 40 41, g32p_row17_traceSegment_088_0243_0040, g32p_row17_traceSegment_088_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_088 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 162 81 81, g32p_row17_traceSegment_088_0162_0081, g32p_row17_traceSegment_088_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_088 0 324 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 0 162 162, g32p_row17_traceSegment_088_0000_0162, g32p_row17_traceSegment_088_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 324 10 10, g32p_row17_traceSegment_088_0324_0010, g32p_row17_traceSegment_088_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 344 10 10, g32p_row17_traceSegment_088_0344_0010, g32p_row17_traceSegment_088_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 324 20 20, g32p_row17_traceSegment_088_0324_0020, g32p_row17_traceSegment_088_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 364 10 10, g32p_row17_traceSegment_088_0364_0010, g32p_row17_traceSegment_088_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 384 10 11, g32p_row17_traceSegment_088_0384_0010, g32p_row17_traceSegment_088_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 364 20 21, g32p_row17_traceSegment_088_0364_0020, g32p_row17_traceSegment_088_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 324 40 41, g32p_row17_traceSegment_088_0324_0040, g32p_row17_traceSegment_088_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 405 10 10, g32p_row17_traceSegment_088_0405_0010, g32p_row17_traceSegment_088_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 425 10 10, g32p_row17_traceSegment_088_0425_0010, g32p_row17_traceSegment_088_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 405 20 20, g32p_row17_traceSegment_088_0405_0020, g32p_row17_traceSegment_088_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 445 10 10, g32p_row17_traceSegment_088_0445_0010, g32p_row17_traceSegment_088_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 465 10 11, g32p_row17_traceSegment_088_0465_0010, g32p_row17_traceSegment_088_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 445 20 21, g32p_row17_traceSegment_088_0445_0020, g32p_row17_traceSegment_088_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 405 40 41, g32p_row17_traceSegment_088_0405_0040, g32p_row17_traceSegment_088_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_088 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 324 81 81, g32p_row17_traceSegment_088_0324_0081, g32p_row17_traceSegment_088_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 486 10 10, g32p_row17_traceSegment_088_0486_0010, g32p_row17_traceSegment_088_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 506 10 10, g32p_row17_traceSegment_088_0506_0010, g32p_row17_traceSegment_088_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 486 20 20, g32p_row17_traceSegment_088_0486_0020, g32p_row17_traceSegment_088_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 526 10 10, g32p_row17_traceSegment_088_0526_0010, g32p_row17_traceSegment_088_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 546 10 11, g32p_row17_traceSegment_088_0546_0010, g32p_row17_traceSegment_088_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 526 20 21, g32p_row17_traceSegment_088_0526_0020, g32p_row17_traceSegment_088_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 486 40 41, g32p_row17_traceSegment_088_0486_0040, g32p_row17_traceSegment_088_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 567 10 10, g32p_row17_traceSegment_088_0567_0010, g32p_row17_traceSegment_088_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 587 10 10, g32p_row17_traceSegment_088_0587_0010, g32p_row17_traceSegment_088_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 567 20 20, g32p_row17_traceSegment_088_0567_0020, g32p_row17_traceSegment_088_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 607 10 10, g32p_row17_traceSegment_088_0607_0010, g32p_row17_traceSegment_088_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 627 10 11, g32p_row17_traceSegment_088_0627_0010, g32p_row17_traceSegment_088_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 607 20 21, g32p_row17_traceSegment_088_0607_0020, g32p_row17_traceSegment_088_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 567 40 41, g32p_row17_traceSegment_088_0567_0040, g32p_row17_traceSegment_088_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_088 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 486 81 81, g32p_row17_traceSegment_088_0486_0081, g32p_row17_traceSegment_088_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_088 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 324 162 162, g32p_row17_traceSegment_088_0324_0162, g32p_row17_traceSegment_088_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_088 0 648 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 0 324 324, g32p_row17_traceSegment_088_0000_0324, g32p_row17_traceSegment_088_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 648 10 10, g32p_row17_traceSegment_088_0648_0010, g32p_row17_traceSegment_088_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 668 10 10, g32p_row17_traceSegment_088_0668_0010, g32p_row17_traceSegment_088_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 648 20 20, g32p_row17_traceSegment_088_0648_0020, g32p_row17_traceSegment_088_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 688 10 10, g32p_row17_traceSegment_088_0688_0010, g32p_row17_traceSegment_088_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 708 10 11, g32p_row17_traceSegment_088_0708_0010, g32p_row17_traceSegment_088_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 688 20 21, g32p_row17_traceSegment_088_0688_0020, g32p_row17_traceSegment_088_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 648 40 41, g32p_row17_traceSegment_088_0648_0040, g32p_row17_traceSegment_088_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 729 10 10, g32p_row17_traceSegment_088_0729_0010, g32p_row17_traceSegment_088_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 749 10 10, g32p_row17_traceSegment_088_0749_0010, g32p_row17_traceSegment_088_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 729 20 20, g32p_row17_traceSegment_088_0729_0020, g32p_row17_traceSegment_088_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 769 10 10, g32p_row17_traceSegment_088_0769_0010, g32p_row17_traceSegment_088_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 789 10 11, g32p_row17_traceSegment_088_0789_0010, g32p_row17_traceSegment_088_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 769 20 21, g32p_row17_traceSegment_088_0769_0020, g32p_row17_traceSegment_088_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 729 40 41, g32p_row17_traceSegment_088_0729_0040, g32p_row17_traceSegment_088_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_088 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 648 81 81, g32p_row17_traceSegment_088_0648_0081, g32p_row17_traceSegment_088_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 810 10 10, g32p_row17_traceSegment_088_0810_0010, g32p_row17_traceSegment_088_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 830 10 10, g32p_row17_traceSegment_088_0830_0010, g32p_row17_traceSegment_088_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 810 20 20, g32p_row17_traceSegment_088_0810_0020, g32p_row17_traceSegment_088_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 850 10 10, g32p_row17_traceSegment_088_0850_0010, g32p_row17_traceSegment_088_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 870 10 11, g32p_row17_traceSegment_088_0870_0010, g32p_row17_traceSegment_088_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 850 20 21, g32p_row17_traceSegment_088_0850_0020, g32p_row17_traceSegment_088_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 810 40 41, g32p_row17_traceSegment_088_0810_0040, g32p_row17_traceSegment_088_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 891 10 10, g32p_row17_traceSegment_088_0891_0010, g32p_row17_traceSegment_088_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 911 10 10, g32p_row17_traceSegment_088_0911_0010, g32p_row17_traceSegment_088_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 891 20 20, g32p_row17_traceSegment_088_0891_0020, g32p_row17_traceSegment_088_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 931 10 10, g32p_row17_traceSegment_088_0931_0010, g32p_row17_traceSegment_088_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 951 10 11, g32p_row17_traceSegment_088_0951_0010, g32p_row17_traceSegment_088_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 931 20 21, g32p_row17_traceSegment_088_0931_0020, g32p_row17_traceSegment_088_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 891 40 41, g32p_row17_traceSegment_088_0891_0040, g32p_row17_traceSegment_088_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_088 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 810 81 81, g32p_row17_traceSegment_088_0810_0081, g32p_row17_traceSegment_088_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_088 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 648 162 162, g32p_row17_traceSegment_088_0648_0162, g32p_row17_traceSegment_088_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 972 10 10, g32p_row17_traceSegment_088_0972_0010, g32p_row17_traceSegment_088_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 992 10 10, g32p_row17_traceSegment_088_0992_0010, g32p_row17_traceSegment_088_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 972 20 20, g32p_row17_traceSegment_088_0972_0020, g32p_row17_traceSegment_088_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1012 10 10, g32p_row17_traceSegment_088_1012_0010, g32p_row17_traceSegment_088_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1032 10 11, g32p_row17_traceSegment_088_1032_0010, g32p_row17_traceSegment_088_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1012 20 21, g32p_row17_traceSegment_088_1012_0020, g32p_row17_traceSegment_088_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 972 40 41, g32p_row17_traceSegment_088_0972_0040, g32p_row17_traceSegment_088_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1053 10 10, g32p_row17_traceSegment_088_1053_0010, g32p_row17_traceSegment_088_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1073 10 10, g32p_row17_traceSegment_088_1073_0010, g32p_row17_traceSegment_088_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1053 20 20, g32p_row17_traceSegment_088_1053_0020, g32p_row17_traceSegment_088_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1093 10 10, g32p_row17_traceSegment_088_1093_0010, g32p_row17_traceSegment_088_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 1123 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 1113 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1113 10 11, g32p_row17_traceSegment_088_1113_0010, g32p_row17_traceSegment_088_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 1093 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1093 20 21, g32p_row17_traceSegment_088_1093_0020, g32p_row17_traceSegment_088_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 1053 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1053 40 41, g32p_row17_traceSegment_088_1053_0040, g32p_row17_traceSegment_088_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_088 972 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 972 81 81, g32p_row17_traceSegment_088_0972_0081, g32p_row17_traceSegment_088_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1134 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 1134 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1134 10 10, g32p_row17_traceSegment_088_1134_0010, g32p_row17_traceSegment_088_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1154 10 10, g32p_row17_traceSegment_088_1154_0010, g32p_row17_traceSegment_088_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 1134 40 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1134 20 20, g32p_row17_traceSegment_088_1134_0020, g32p_row17_traceSegment_088_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1174 10 10, g32p_row17_traceSegment_088_1174_0010, g32p_row17_traceSegment_088_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1194 10 11, g32p_row17_traceSegment_088_1194_0010, g32p_row17_traceSegment_088_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1174 20 21, g32p_row17_traceSegment_088_1174_0020, g32p_row17_traceSegment_088_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 1134 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1134 40 41, g32p_row17_traceSegment_088_1134_0040, g32p_row17_traceSegment_088_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1215 10 10, g32p_row17_traceSegment_088_1215_0010, g32p_row17_traceSegment_088_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1235 10 10, g32p_row17_traceSegment_088_1235_0010, g32p_row17_traceSegment_088_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_088 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1215 20 20, g32p_row17_traceSegment_088_1215_0020, g32p_row17_traceSegment_088_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_088 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1255 10 10, g32p_row17_traceSegment_088_1255_0010, g32p_row17_traceSegment_088_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_088 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_088 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_088_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_088 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1275 10 11, g32p_row17_traceSegment_088_1275_0010, g32p_row17_traceSegment_088_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_088 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1255 20 21, g32p_row17_traceSegment_088_1255_0020, g32p_row17_traceSegment_088_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_088 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1215 40 41, g32p_row17_traceSegment_088_1215_0040, g32p_row17_traceSegment_088_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_088_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_088 1134 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 1134 81 81, g32p_row17_traceSegment_088_1134_0081, g32p_row17_traceSegment_088_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_088 972 324 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 972 162 162, g32p_row17_traceSegment_088_0972_0162, g32p_row17_traceSegment_088_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_088 648 648 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 648 324 324, g32p_row17_traceSegment_088_0648_0324, g32p_row17_traceSegment_088_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_088_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_088 0 1296 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_088 0 648 648, g32p_row17_traceSegment_088_0000_0648, g32p_row17_traceSegment_088_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 88 = [0, 0, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_088_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_089 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 89 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_089_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 0 10 10, g32p_row17_traceSegment_089_0000_0010, g32p_row17_traceSegment_089_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 20 10 10, g32p_row17_traceSegment_089_0020_0010, g32p_row17_traceSegment_089_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 0 20 20, g32p_row17_traceSegment_089_0000_0020, g32p_row17_traceSegment_089_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 40 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 50 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 40 20 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 40 10 10, g32p_row17_traceSegment_089_0040_0010, g32p_row17_traceSegment_089_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 70 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 60 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 60 10 11, g32p_row17_traceSegment_089_0060_0010, g32p_row17_traceSegment_089_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 40 41 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 40 20 21, g32p_row17_traceSegment_089_0040_0020, g32p_row17_traceSegment_089_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 0 81 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 0 40 41, g32p_row17_traceSegment_089_0000_0040, g32p_row17_traceSegment_089_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 81 10 10, g32p_row17_traceSegment_089_0081_0010, g32p_row17_traceSegment_089_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 111 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 101 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 101 10 10, g32p_row17_traceSegment_089_0101_0010, g32p_row17_traceSegment_089_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 81 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 81 20 20, g32p_row17_traceSegment_089_0081_0020, g32p_row17_traceSegment_089_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 121 10 10, g32p_row17_traceSegment_089_0121_0010, g32p_row17_traceSegment_089_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 141 10 11, g32p_row17_traceSegment_089_0141_0010, g32p_row17_traceSegment_089_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 121 20 21, g32p_row17_traceSegment_089_0121_0020, g32p_row17_traceSegment_089_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 81 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 81 40 41, g32p_row17_traceSegment_089_0081_0040, g32p_row17_traceSegment_089_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_089 0 162 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 0 81 81, g32p_row17_traceSegment_089_0000_0081, g32p_row17_traceSegment_089_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 162 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 162 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 162 10 10, g32p_row17_traceSegment_089_0162_0010, g32p_row17_traceSegment_089_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 182 10 10, g32p_row17_traceSegment_089_0182_0010, g32p_row17_traceSegment_089_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 162 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 162 20 20, g32p_row17_traceSegment_089_0162_0020, g32p_row17_traceSegment_089_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 202 10 10, g32p_row17_traceSegment_089_0202_0010, g32p_row17_traceSegment_089_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 222 10 11, g32p_row17_traceSegment_089_0222_0010, g32p_row17_traceSegment_089_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 202 20 21, g32p_row17_traceSegment_089_0202_0020, g32p_row17_traceSegment_089_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 162 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 162 40 41, g32p_row17_traceSegment_089_0162_0040, g32p_row17_traceSegment_089_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 243 10 10, g32p_row17_traceSegment_089_0243_0010, g32p_row17_traceSegment_089_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 263 10 10, g32p_row17_traceSegment_089_0263_0010, g32p_row17_traceSegment_089_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 243 20 20, g32p_row17_traceSegment_089_0243_0020, g32p_row17_traceSegment_089_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 283 10 10, g32p_row17_traceSegment_089_0283_0010, g32p_row17_traceSegment_089_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 303 10 11, g32p_row17_traceSegment_089_0303_0010, g32p_row17_traceSegment_089_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 283 20 21, g32p_row17_traceSegment_089_0283_0020, g32p_row17_traceSegment_089_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 243 40 41, g32p_row17_traceSegment_089_0243_0040, g32p_row17_traceSegment_089_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_089 162 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 162 81 81, g32p_row17_traceSegment_089_0162_0081, g32p_row17_traceSegment_089_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_089 0 324 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 0 162 162, g32p_row17_traceSegment_089_0000_0162, g32p_row17_traceSegment_089_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 324 10 10, g32p_row17_traceSegment_089_0324_0010, g32p_row17_traceSegment_089_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 344 10 10, g32p_row17_traceSegment_089_0344_0010, g32p_row17_traceSegment_089_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 324 20 20, g32p_row17_traceSegment_089_0324_0020, g32p_row17_traceSegment_089_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 364 10 10, g32p_row17_traceSegment_089_0364_0010, g32p_row17_traceSegment_089_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 384 10 11, g32p_row17_traceSegment_089_0384_0010, g32p_row17_traceSegment_089_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 364 20 21, g32p_row17_traceSegment_089_0364_0020, g32p_row17_traceSegment_089_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 324 40 41, g32p_row17_traceSegment_089_0324_0040, g32p_row17_traceSegment_089_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 405 10 10, g32p_row17_traceSegment_089_0405_0010, g32p_row17_traceSegment_089_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 425 10 10, g32p_row17_traceSegment_089_0425_0010, g32p_row17_traceSegment_089_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 405 20 20, g32p_row17_traceSegment_089_0405_0020, g32p_row17_traceSegment_089_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 445 10 10, g32p_row17_traceSegment_089_0445_0010, g32p_row17_traceSegment_089_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 465 10 11, g32p_row17_traceSegment_089_0465_0010, g32p_row17_traceSegment_089_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 445 20 21, g32p_row17_traceSegment_089_0445_0020, g32p_row17_traceSegment_089_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 405 40 41, g32p_row17_traceSegment_089_0405_0040, g32p_row17_traceSegment_089_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_089 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 324 81 81, g32p_row17_traceSegment_089_0324_0081, g32p_row17_traceSegment_089_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 486 10 10, g32p_row17_traceSegment_089_0486_0010, g32p_row17_traceSegment_089_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 506 10 10, g32p_row17_traceSegment_089_0506_0010, g32p_row17_traceSegment_089_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 486 20 20, g32p_row17_traceSegment_089_0486_0020, g32p_row17_traceSegment_089_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 526 10 10, g32p_row17_traceSegment_089_0526_0010, g32p_row17_traceSegment_089_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 556 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 546 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 546 10 11, g32p_row17_traceSegment_089_0546_0010, g32p_row17_traceSegment_089_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 526 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 526 20 21, g32p_row17_traceSegment_089_0526_0020, g32p_row17_traceSegment_089_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 486 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 486 40 41, g32p_row17_traceSegment_089_0486_0040, g32p_row17_traceSegment_089_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 567 10 10, g32p_row17_traceSegment_089_0567_0010, g32p_row17_traceSegment_089_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 587 10 10, g32p_row17_traceSegment_089_0587_0010, g32p_row17_traceSegment_089_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 567 20 20, g32p_row17_traceSegment_089_0567_0020, g32p_row17_traceSegment_089_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 607 10 10, g32p_row17_traceSegment_089_0607_0010, g32p_row17_traceSegment_089_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 627 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 627 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 627 10 11, g32p_row17_traceSegment_089_0627_0010, g32p_row17_traceSegment_089_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 607 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 607 20 21, g32p_row17_traceSegment_089_0607_0020, g32p_row17_traceSegment_089_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 567 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 567 40 41, g32p_row17_traceSegment_089_0567_0040, g32p_row17_traceSegment_089_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_089 486 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 486 81 81, g32p_row17_traceSegment_089_0486_0081, g32p_row17_traceSegment_089_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_089 324 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 324 162 162, g32p_row17_traceSegment_089_0324_0162, g32p_row17_traceSegment_089_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_089 0 648 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 0 324 324, g32p_row17_traceSegment_089_0000_0324, g32p_row17_traceSegment_089_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 648 10 10, g32p_row17_traceSegment_089_0648_0010, g32p_row17_traceSegment_089_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 668 10 10, g32p_row17_traceSegment_089_0668_0010, g32p_row17_traceSegment_089_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 648 20 20, g32p_row17_traceSegment_089_0648_0020, g32p_row17_traceSegment_089_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 698 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 688 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 688 10 10, g32p_row17_traceSegment_089_0688_0010, g32p_row17_traceSegment_089_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 708 10 11, g32p_row17_traceSegment_089_0708_0010, g32p_row17_traceSegment_089_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 688 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 688 20 21, g32p_row17_traceSegment_089_0688_0020, g32p_row17_traceSegment_089_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 648 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 648 40 41, g32p_row17_traceSegment_089_0648_0040, g32p_row17_traceSegment_089_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 729 10 10, g32p_row17_traceSegment_089_0729_0010, g32p_row17_traceSegment_089_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 749 10 10, g32p_row17_traceSegment_089_0749_0010, g32p_row17_traceSegment_089_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 729 20 20, g32p_row17_traceSegment_089_0729_0020, g32p_row17_traceSegment_089_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 769 10 10, g32p_row17_traceSegment_089_0769_0010, g32p_row17_traceSegment_089_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 799 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 789 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 789 10 11, g32p_row17_traceSegment_089_0789_0010, g32p_row17_traceSegment_089_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 769 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 769 20 21, g32p_row17_traceSegment_089_0769_0020, g32p_row17_traceSegment_089_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 729 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 729 40 41, g32p_row17_traceSegment_089_0729_0040, g32p_row17_traceSegment_089_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_089 648 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 648 81 81, g32p_row17_traceSegment_089_0648_0081, g32p_row17_traceSegment_089_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 810 10 10, g32p_row17_traceSegment_089_0810_0010, g32p_row17_traceSegment_089_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 830 10 10, g32p_row17_traceSegment_089_0830_0010, g32p_row17_traceSegment_089_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 810 20 20, g32p_row17_traceSegment_089_0810_0020, g32p_row17_traceSegment_089_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 850 10 10, g32p_row17_traceSegment_089_0850_0010, g32p_row17_traceSegment_089_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 870 10 11, g32p_row17_traceSegment_089_0870_0010, g32p_row17_traceSegment_089_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 850 20 21, g32p_row17_traceSegment_089_0850_0020, g32p_row17_traceSegment_089_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 810 40 41, g32p_row17_traceSegment_089_0810_0040, g32p_row17_traceSegment_089_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 891 10 10, g32p_row17_traceSegment_089_0891_0010, g32p_row17_traceSegment_089_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 911 10 10, g32p_row17_traceSegment_089_0911_0010, g32p_row17_traceSegment_089_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 891 20 20, g32p_row17_traceSegment_089_0891_0020, g32p_row17_traceSegment_089_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 931 10 10, g32p_row17_traceSegment_089_0931_0010, g32p_row17_traceSegment_089_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 951 10 11, g32p_row17_traceSegment_089_0951_0010, g32p_row17_traceSegment_089_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 931 20 21, g32p_row17_traceSegment_089_0931_0020, g32p_row17_traceSegment_089_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 891 40 41, g32p_row17_traceSegment_089_0891_0040, g32p_row17_traceSegment_089_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_089 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 810 81 81, g32p_row17_traceSegment_089_0810_0081, g32p_row17_traceSegment_089_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_089 648 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 648 162 162, g32p_row17_traceSegment_089_0648_0162, g32p_row17_traceSegment_089_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 972 10 10, g32p_row17_traceSegment_089_0972_0010, g32p_row17_traceSegment_089_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 992 10 10, g32p_row17_traceSegment_089_0992_0010, g32p_row17_traceSegment_089_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 972 20 20, g32p_row17_traceSegment_089_0972_0020, g32p_row17_traceSegment_089_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1012 10 10, g32p_row17_traceSegment_089_1012_0010, g32p_row17_traceSegment_089_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1032 10 11, g32p_row17_traceSegment_089_1032_0010, g32p_row17_traceSegment_089_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1012 20 21, g32p_row17_traceSegment_089_1012_0020, g32p_row17_traceSegment_089_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 972 40 41, g32p_row17_traceSegment_089_0972_0040, g32p_row17_traceSegment_089_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1053 10 10, g32p_row17_traceSegment_089_1053_0010, g32p_row17_traceSegment_089_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1073 10 10, g32p_row17_traceSegment_089_1073_0010, g32p_row17_traceSegment_089_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1053 20 20, g32p_row17_traceSegment_089_1053_0020, g32p_row17_traceSegment_089_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1093 10 10, g32p_row17_traceSegment_089_1093_0010, g32p_row17_traceSegment_089_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1113 10 11, g32p_row17_traceSegment_089_1113_0010, g32p_row17_traceSegment_089_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1093 20 21, g32p_row17_traceSegment_089_1093_0020, g32p_row17_traceSegment_089_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1053 40 41, g32p_row17_traceSegment_089_1053_0040, g32p_row17_traceSegment_089_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_089 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 972 81 81, g32p_row17_traceSegment_089_0972_0081, g32p_row17_traceSegment_089_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1134 10 10, g32p_row17_traceSegment_089_1134_0010, g32p_row17_traceSegment_089_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1154 10 10, g32p_row17_traceSegment_089_1154_0010, g32p_row17_traceSegment_089_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1134 20 20, g32p_row17_traceSegment_089_1134_0020, g32p_row17_traceSegment_089_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1174 10 10, g32p_row17_traceSegment_089_1174_0010, g32p_row17_traceSegment_089_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1194 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 1194 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1194 10 11, g32p_row17_traceSegment_089_1194_0010, g32p_row17_traceSegment_089_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 1174 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1174 20 21, g32p_row17_traceSegment_089_1174_0020, g32p_row17_traceSegment_089_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 1134 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1134 40 41, g32p_row17_traceSegment_089_1134_0040, g32p_row17_traceSegment_089_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1215 10 10, g32p_row17_traceSegment_089_1215_0010, g32p_row17_traceSegment_089_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1245 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 1235 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1235 10 10, g32p_row17_traceSegment_089_1235_0010, g32p_row17_traceSegment_089_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_089 1215 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1215 20 20, g32p_row17_traceSegment_089_1215_0020, g32p_row17_traceSegment_089_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_089 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1255 10 10, g32p_row17_traceSegment_089_1255_0010, g32p_row17_traceSegment_089_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_089 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_089 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_089_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_089 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1275 10 11, g32p_row17_traceSegment_089_1275_0010, g32p_row17_traceSegment_089_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_089 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1255 20 21, g32p_row17_traceSegment_089_1255_0020, g32p_row17_traceSegment_089_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_089 1215 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1215 40 41, g32p_row17_traceSegment_089_1215_0040, g32p_row17_traceSegment_089_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_089_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_089 1134 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 1134 81 81, g32p_row17_traceSegment_089_1134_0081, g32p_row17_traceSegment_089_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_089 972 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 972 162 162, g32p_row17_traceSegment_089_0972_0162, g32p_row17_traceSegment_089_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_089 648 648 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 648 324 324, g32p_row17_traceSegment_089_0648_0324, g32p_row17_traceSegment_089_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_089_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_089 0 1296 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_089 0 648 648, g32p_row17_traceSegment_089_0000_0648, g32p_row17_traceSegment_089_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_089 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 89 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_089_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_tracePolynomial_081 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 81) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 81) (g32p_literalTraceValue 16 81)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_081]
  decide +kernel

theorem g32p_row17_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 82) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 82) (g32p_literalTraceValue 16 82)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_082]
  decide +kernel

theorem g32p_row17_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 84) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 84) (g32p_literalTraceValue 16 84)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_084]
  decide +kernel

theorem g32p_row17_tracePolynomial_085 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 85) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 85) (g32p_literalTraceValue 16 85)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_085]
  decide +kernel

theorem g32p_row17_tracePolynomial_086 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 86) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 86) (g32p_literalTraceValue 16 86)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_086]
  decide +kernel

theorem g32p_row17_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 87) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 87) (g32p_literalTraceValue 16 87)
      [1, -1, 1] [15552, 15552, 15552] = true := by
  rw [g32p_row17_traceCoefficients_087]
  decide +kernel

theorem g32p_row17_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 88) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 88) (g32p_literalTraceValue 16 88)
      [1, -1, 1] [15552, 15552, 15552] = true := by
  rw [g32p_row17_traceCoefficients_088]
  decide +kernel

theorem g32p_row17_tracePolynomial_089 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 89) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 89) (g32p_literalTraceValue 16 89)
      [1, -1, 1] [5184, 5184, 5184] = true := by
  rw [g32p_row17_traceCoefficients_089]
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

private def g32p_row17_traceSegment_091 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 91 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_091_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 0 10 10, g32p_row17_traceSegment_091_0000_0010, g32p_row17_traceSegment_091_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 20 10 10, g32p_row17_traceSegment_091_0020_0010, g32p_row17_traceSegment_091_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 0 20 20, g32p_row17_traceSegment_091_0000_0020, g32p_row17_traceSegment_091_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 40 10 10, g32p_row17_traceSegment_091_0040_0010, g32p_row17_traceSegment_091_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 60 10 11, g32p_row17_traceSegment_091_0060_0010, g32p_row17_traceSegment_091_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 40 20 21, g32p_row17_traceSegment_091_0040_0020, g32p_row17_traceSegment_091_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 0 40 41, g32p_row17_traceSegment_091_0000_0040, g32p_row17_traceSegment_091_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 81 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 91 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 81 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 81 10 10, g32p_row17_traceSegment_091_0081_0010, g32p_row17_traceSegment_091_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 101 10 10, g32p_row17_traceSegment_091_0101_0010, g32p_row17_traceSegment_091_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 81 40 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 81 20 20, g32p_row17_traceSegment_091_0081_0020, g32p_row17_traceSegment_091_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 121 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 121 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 121 10 10, g32p_row17_traceSegment_091_0121_0010, g32p_row17_traceSegment_091_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 151 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 141 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 141 10 11, g32p_row17_traceSegment_091_0141_0010, g32p_row17_traceSegment_091_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 121 41 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 121 20 21, g32p_row17_traceSegment_091_0121_0020, g32p_row17_traceSegment_091_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 81 81 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 81 40 41, g32p_row17_traceSegment_091_0081_0040, g32p_row17_traceSegment_091_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_091 0 162 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 0 81 81, g32p_row17_traceSegment_091_0000_0081, g32p_row17_traceSegment_091_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 162 10 10, g32p_row17_traceSegment_091_0162_0010, g32p_row17_traceSegment_091_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 182 10 10, g32p_row17_traceSegment_091_0182_0010, g32p_row17_traceSegment_091_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 162 20 20, g32p_row17_traceSegment_091_0162_0020, g32p_row17_traceSegment_091_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 202 10 10, g32p_row17_traceSegment_091_0202_0010, g32p_row17_traceSegment_091_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 222 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 222 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 222 10 11, g32p_row17_traceSegment_091_0222_0010, g32p_row17_traceSegment_091_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 202 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 202 20 21, g32p_row17_traceSegment_091_0202_0020, g32p_row17_traceSegment_091_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 162 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 162 40 41, g32p_row17_traceSegment_091_0162_0040, g32p_row17_traceSegment_091_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 243 10 10, g32p_row17_traceSegment_091_0243_0010, g32p_row17_traceSegment_091_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 263 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 263 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 263 10 10, g32p_row17_traceSegment_091_0263_0010, g32p_row17_traceSegment_091_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 243 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 243 20 20, g32p_row17_traceSegment_091_0243_0020, g32p_row17_traceSegment_091_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 283 10 10, g32p_row17_traceSegment_091_0283_0010, g32p_row17_traceSegment_091_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 303 10 11, g32p_row17_traceSegment_091_0303_0010, g32p_row17_traceSegment_091_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 283 20 21, g32p_row17_traceSegment_091_0283_0020, g32p_row17_traceSegment_091_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 243 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 243 40 41, g32p_row17_traceSegment_091_0243_0040, g32p_row17_traceSegment_091_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_091 162 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 162 81 81, g32p_row17_traceSegment_091_0162_0081, g32p_row17_traceSegment_091_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_091 0 324 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 0 162 162, g32p_row17_traceSegment_091_0000_0162, g32p_row17_traceSegment_091_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 324 10 10, g32p_row17_traceSegment_091_0324_0010, g32p_row17_traceSegment_091_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 344 10 10, g32p_row17_traceSegment_091_0344_0010, g32p_row17_traceSegment_091_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 324 20 20, g32p_row17_traceSegment_091_0324_0020, g32p_row17_traceSegment_091_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 364 10 10, g32p_row17_traceSegment_091_0364_0010, g32p_row17_traceSegment_091_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 384 10 11, g32p_row17_traceSegment_091_0384_0010, g32p_row17_traceSegment_091_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 364 20 21, g32p_row17_traceSegment_091_0364_0020, g32p_row17_traceSegment_091_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 324 40 41, g32p_row17_traceSegment_091_0324_0040, g32p_row17_traceSegment_091_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 415 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 405 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 405 10 10, g32p_row17_traceSegment_091_0405_0010, g32p_row17_traceSegment_091_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 425 10 10, g32p_row17_traceSegment_091_0425_0010, g32p_row17_traceSegment_091_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 405 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 405 20 20, g32p_row17_traceSegment_091_0405_0020, g32p_row17_traceSegment_091_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 445 10 10, g32p_row17_traceSegment_091_0445_0010, g32p_row17_traceSegment_091_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 475 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 465 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 465 10 11, g32p_row17_traceSegment_091_0465_0010, g32p_row17_traceSegment_091_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 445 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 445 20 21, g32p_row17_traceSegment_091_0445_0020, g32p_row17_traceSegment_091_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 405 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 405 40 41, g32p_row17_traceSegment_091_0405_0040, g32p_row17_traceSegment_091_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_091 324 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 324 81 81, g32p_row17_traceSegment_091_0324_0081, g32p_row17_traceSegment_091_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 486 10 10, g32p_row17_traceSegment_091_0486_0010, g32p_row17_traceSegment_091_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 506 10 10, g32p_row17_traceSegment_091_0506_0010, g32p_row17_traceSegment_091_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 486 20 20, g32p_row17_traceSegment_091_0486_0020, g32p_row17_traceSegment_091_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 526 10 10, g32p_row17_traceSegment_091_0526_0010, g32p_row17_traceSegment_091_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 546 10 11, g32p_row17_traceSegment_091_0546_0010, g32p_row17_traceSegment_091_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 526 20 21, g32p_row17_traceSegment_091_0526_0020, g32p_row17_traceSegment_091_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 486 40 41, g32p_row17_traceSegment_091_0486_0040, g32p_row17_traceSegment_091_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 567 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 567 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 567 10 10, g32p_row17_traceSegment_091_0567_0010, g32p_row17_traceSegment_091_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 587 10 10, g32p_row17_traceSegment_091_0587_0010, g32p_row17_traceSegment_091_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 567 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 567 20 20, g32p_row17_traceSegment_091_0567_0020, g32p_row17_traceSegment_091_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 607 10 10, g32p_row17_traceSegment_091_0607_0010, g32p_row17_traceSegment_091_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 637 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 627 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 627 10 11, g32p_row17_traceSegment_091_0627_0010, g32p_row17_traceSegment_091_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 607 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 607 20 21, g32p_row17_traceSegment_091_0607_0020, g32p_row17_traceSegment_091_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 567 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 567 40 41, g32p_row17_traceSegment_091_0567_0040, g32p_row17_traceSegment_091_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_091 486 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 486 81 81, g32p_row17_traceSegment_091_0486_0081, g32p_row17_traceSegment_091_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_091 324 324 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 324 162 162, g32p_row17_traceSegment_091_0324_0162, g32p_row17_traceSegment_091_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_091 0 648 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 0 324 324, g32p_row17_traceSegment_091_0000_0324, g32p_row17_traceSegment_091_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 648 10 10, g32p_row17_traceSegment_091_0648_0010, g32p_row17_traceSegment_091_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 668 10 10, g32p_row17_traceSegment_091_0668_0010, g32p_row17_traceSegment_091_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 648 20 20, g32p_row17_traceSegment_091_0648_0020, g32p_row17_traceSegment_091_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 688 10 10, g32p_row17_traceSegment_091_0688_0010, g32p_row17_traceSegment_091_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 718 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 708 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 708 10 11, g32p_row17_traceSegment_091_0708_0010, g32p_row17_traceSegment_091_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 688 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 688 20 21, g32p_row17_traceSegment_091_0688_0020, g32p_row17_traceSegment_091_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 648 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 648 40 41, g32p_row17_traceSegment_091_0648_0040, g32p_row17_traceSegment_091_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 729 10 10, g32p_row17_traceSegment_091_0729_0010, g32p_row17_traceSegment_091_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 749 10 10, g32p_row17_traceSegment_091_0749_0010, g32p_row17_traceSegment_091_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 729 20 20, g32p_row17_traceSegment_091_0729_0020, g32p_row17_traceSegment_091_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 769 10 10, g32p_row17_traceSegment_091_0769_0010, g32p_row17_traceSegment_091_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 789 10 11, g32p_row17_traceSegment_091_0789_0010, g32p_row17_traceSegment_091_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 769 20 21, g32p_row17_traceSegment_091_0769_0020, g32p_row17_traceSegment_091_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 729 40 41, g32p_row17_traceSegment_091_0729_0040, g32p_row17_traceSegment_091_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_091 648 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 648 81 81, g32p_row17_traceSegment_091_0648_0081, g32p_row17_traceSegment_091_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 810 10 10, g32p_row17_traceSegment_091_0810_0010, g32p_row17_traceSegment_091_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 830 10 10, g32p_row17_traceSegment_091_0830_0010, g32p_row17_traceSegment_091_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 810 20 20, g32p_row17_traceSegment_091_0810_0020, g32p_row17_traceSegment_091_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 850 10 10, g32p_row17_traceSegment_091_0850_0010, g32p_row17_traceSegment_091_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 870 10 11, g32p_row17_traceSegment_091_0870_0010, g32p_row17_traceSegment_091_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 850 20 21, g32p_row17_traceSegment_091_0850_0020, g32p_row17_traceSegment_091_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 810 40 41, g32p_row17_traceSegment_091_0810_0040, g32p_row17_traceSegment_091_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 891 10 10, g32p_row17_traceSegment_091_0891_0010, g32p_row17_traceSegment_091_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 911 10 10, g32p_row17_traceSegment_091_0911_0010, g32p_row17_traceSegment_091_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 891 20 20, g32p_row17_traceSegment_091_0891_0020, g32p_row17_traceSegment_091_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 931 10 10, g32p_row17_traceSegment_091_0931_0010, g32p_row17_traceSegment_091_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 951 10 11, g32p_row17_traceSegment_091_0951_0010, g32p_row17_traceSegment_091_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 931 20 21, g32p_row17_traceSegment_091_0931_0020, g32p_row17_traceSegment_091_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 891 40 41, g32p_row17_traceSegment_091_0891_0040, g32p_row17_traceSegment_091_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_091 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 810 81 81, g32p_row17_traceSegment_091_0810_0081, g32p_row17_traceSegment_091_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_091 648 324 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 648 162 162, g32p_row17_traceSegment_091_0648_0162, g32p_row17_traceSegment_091_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 972 10 10, g32p_row17_traceSegment_091_0972_0010, g32p_row17_traceSegment_091_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 992 10 10, g32p_row17_traceSegment_091_0992_0010, g32p_row17_traceSegment_091_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 972 20 20, g32p_row17_traceSegment_091_0972_0020, g32p_row17_traceSegment_091_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1012 10 10, g32p_row17_traceSegment_091_1012_0010, g32p_row17_traceSegment_091_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1032 10 11, g32p_row17_traceSegment_091_1032_0010, g32p_row17_traceSegment_091_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1012 20 21, g32p_row17_traceSegment_091_1012_0020, g32p_row17_traceSegment_091_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 972 40 41, g32p_row17_traceSegment_091_0972_0040, g32p_row17_traceSegment_091_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1053 10 10, g32p_row17_traceSegment_091_1053_0010, g32p_row17_traceSegment_091_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1073 10 10, g32p_row17_traceSegment_091_1073_0010, g32p_row17_traceSegment_091_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1053 20 20, g32p_row17_traceSegment_091_1053_0020, g32p_row17_traceSegment_091_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1093 10 10, g32p_row17_traceSegment_091_1093_0010, g32p_row17_traceSegment_091_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1113 10 11, g32p_row17_traceSegment_091_1113_0010, g32p_row17_traceSegment_091_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1093 20 21, g32p_row17_traceSegment_091_1093_0020, g32p_row17_traceSegment_091_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1053 40 41, g32p_row17_traceSegment_091_1053_0040, g32p_row17_traceSegment_091_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_091 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 972 81 81, g32p_row17_traceSegment_091_0972_0081, g32p_row17_traceSegment_091_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1134 10 10, g32p_row17_traceSegment_091_1134_0010, g32p_row17_traceSegment_091_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1154 10 10, g32p_row17_traceSegment_091_1154_0010, g32p_row17_traceSegment_091_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1134 20 20, g32p_row17_traceSegment_091_1134_0020, g32p_row17_traceSegment_091_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1174 10 10, g32p_row17_traceSegment_091_1174_0010, g32p_row17_traceSegment_091_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1194 10 11, g32p_row17_traceSegment_091_1194_0010, g32p_row17_traceSegment_091_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1174 20 21, g32p_row17_traceSegment_091_1174_0020, g32p_row17_traceSegment_091_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1134 40 41, g32p_row17_traceSegment_091_1134_0040, g32p_row17_traceSegment_091_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1215 10 10, g32p_row17_traceSegment_091_1215_0010, g32p_row17_traceSegment_091_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1235 10 10, g32p_row17_traceSegment_091_1235_0010, g32p_row17_traceSegment_091_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_091 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1215 20 20, g32p_row17_traceSegment_091_1215_0020, g32p_row17_traceSegment_091_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1265 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_091 1255 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1255 10 10, g32p_row17_traceSegment_091_1255_0010, g32p_row17_traceSegment_091_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_091 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_091 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_091_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_091 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1275 10 11, g32p_row17_traceSegment_091_1275_0010, g32p_row17_traceSegment_091_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_091 1255 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1255 20 21, g32p_row17_traceSegment_091_1255_0020, g32p_row17_traceSegment_091_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_091 1215 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1215 40 41, g32p_row17_traceSegment_091_1215_0040, g32p_row17_traceSegment_091_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_091_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_091 1134 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 1134 81 81, g32p_row17_traceSegment_091_1134_0081, g32p_row17_traceSegment_091_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_091 972 324 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 972 162 162, g32p_row17_traceSegment_091_0972_0162, g32p_row17_traceSegment_091_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_091 648 648 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 648 324 324, g32p_row17_traceSegment_091_0648_0324, g32p_row17_traceSegment_091_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_091_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_091 0 1296 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_091 0 648 648, g32p_row17_traceSegment_091_0000_0648, g32p_row17_traceSegment_091_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_091 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 91 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_091_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_092 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 92 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_092_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 0 10 10, g32p_row17_traceSegment_092_0000_0010, g32p_row17_traceSegment_092_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 20 10 10, g32p_row17_traceSegment_092_0020_0010, g32p_row17_traceSegment_092_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 0 20 20, g32p_row17_traceSegment_092_0000_0020, g32p_row17_traceSegment_092_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 40 10 10, g32p_row17_traceSegment_092_0040_0010, g32p_row17_traceSegment_092_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 60 10 11, g32p_row17_traceSegment_092_0060_0010, g32p_row17_traceSegment_092_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 40 20 21, g32p_row17_traceSegment_092_0040_0020, g32p_row17_traceSegment_092_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 0 40 41, g32p_row17_traceSegment_092_0000_0040, g32p_row17_traceSegment_092_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 81 10 10, g32p_row17_traceSegment_092_0081_0010, g32p_row17_traceSegment_092_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 101 10 10, g32p_row17_traceSegment_092_0101_0010, g32p_row17_traceSegment_092_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 81 20 20, g32p_row17_traceSegment_092_0081_0020, g32p_row17_traceSegment_092_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 121 10 10, g32p_row17_traceSegment_092_0121_0010, g32p_row17_traceSegment_092_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 141 10 11, g32p_row17_traceSegment_092_0141_0010, g32p_row17_traceSegment_092_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 121 20 21, g32p_row17_traceSegment_092_0121_0020, g32p_row17_traceSegment_092_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 81 40 41, g32p_row17_traceSegment_092_0081_0040, g32p_row17_traceSegment_092_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_092 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 0 81 81, g32p_row17_traceSegment_092_0000_0081, g32p_row17_traceSegment_092_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 162 10 10, g32p_row17_traceSegment_092_0162_0010, g32p_row17_traceSegment_092_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 182 10 10, g32p_row17_traceSegment_092_0182_0010, g32p_row17_traceSegment_092_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 162 20 20, g32p_row17_traceSegment_092_0162_0020, g32p_row17_traceSegment_092_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 202 10 10, g32p_row17_traceSegment_092_0202_0010, g32p_row17_traceSegment_092_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 222 10 11, g32p_row17_traceSegment_092_0222_0010, g32p_row17_traceSegment_092_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 202 20 21, g32p_row17_traceSegment_092_0202_0020, g32p_row17_traceSegment_092_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 162 40 41, g32p_row17_traceSegment_092_0162_0040, g32p_row17_traceSegment_092_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 243 10 10, g32p_row17_traceSegment_092_0243_0010, g32p_row17_traceSegment_092_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 263 10 10, g32p_row17_traceSegment_092_0263_0010, g32p_row17_traceSegment_092_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 243 20 20, g32p_row17_traceSegment_092_0243_0020, g32p_row17_traceSegment_092_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 283 10 10, g32p_row17_traceSegment_092_0283_0010, g32p_row17_traceSegment_092_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 303 10 11, g32p_row17_traceSegment_092_0303_0010, g32p_row17_traceSegment_092_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 283 20 21, g32p_row17_traceSegment_092_0283_0020, g32p_row17_traceSegment_092_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 243 40 41, g32p_row17_traceSegment_092_0243_0040, g32p_row17_traceSegment_092_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_092 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 162 81 81, g32p_row17_traceSegment_092_0162_0081, g32p_row17_traceSegment_092_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_092 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 0 162 162, g32p_row17_traceSegment_092_0000_0162, g32p_row17_traceSegment_092_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 324 10 10, g32p_row17_traceSegment_092_0324_0010, g32p_row17_traceSegment_092_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 344 10 10, g32p_row17_traceSegment_092_0344_0010, g32p_row17_traceSegment_092_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 324 20 20, g32p_row17_traceSegment_092_0324_0020, g32p_row17_traceSegment_092_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 364 10 10, g32p_row17_traceSegment_092_0364_0010, g32p_row17_traceSegment_092_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 384 10 11, g32p_row17_traceSegment_092_0384_0010, g32p_row17_traceSegment_092_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 364 20 21, g32p_row17_traceSegment_092_0364_0020, g32p_row17_traceSegment_092_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 324 40 41, g32p_row17_traceSegment_092_0324_0040, g32p_row17_traceSegment_092_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 405 10 10, g32p_row17_traceSegment_092_0405_0010, g32p_row17_traceSegment_092_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 425 10 10, g32p_row17_traceSegment_092_0425_0010, g32p_row17_traceSegment_092_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 405 20 20, g32p_row17_traceSegment_092_0405_0020, g32p_row17_traceSegment_092_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 445 10 10, g32p_row17_traceSegment_092_0445_0010, g32p_row17_traceSegment_092_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 465 10 11, g32p_row17_traceSegment_092_0465_0010, g32p_row17_traceSegment_092_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 445 20 21, g32p_row17_traceSegment_092_0445_0020, g32p_row17_traceSegment_092_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 405 40 41, g32p_row17_traceSegment_092_0405_0040, g32p_row17_traceSegment_092_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_092 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 324 81 81, g32p_row17_traceSegment_092_0324_0081, g32p_row17_traceSegment_092_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 486 10 10, g32p_row17_traceSegment_092_0486_0010, g32p_row17_traceSegment_092_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 506 10 10, g32p_row17_traceSegment_092_0506_0010, g32p_row17_traceSegment_092_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 486 20 20, g32p_row17_traceSegment_092_0486_0020, g32p_row17_traceSegment_092_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 526 10 10, g32p_row17_traceSegment_092_0526_0010, g32p_row17_traceSegment_092_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 556 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 546 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 546 10 11, g32p_row17_traceSegment_092_0546_0010, g32p_row17_traceSegment_092_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 526 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 526 20 21, g32p_row17_traceSegment_092_0526_0020, g32p_row17_traceSegment_092_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 486 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 486 40 41, g32p_row17_traceSegment_092_0486_0040, g32p_row17_traceSegment_092_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 567 10 10, g32p_row17_traceSegment_092_0567_0010, g32p_row17_traceSegment_092_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 587 10 10, g32p_row17_traceSegment_092_0587_0010, g32p_row17_traceSegment_092_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 567 20 20, g32p_row17_traceSegment_092_0567_0020, g32p_row17_traceSegment_092_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 607 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 607 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 607 10 10, g32p_row17_traceSegment_092_0607_0010, g32p_row17_traceSegment_092_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 627 10 11, g32p_row17_traceSegment_092_0627_0010, g32p_row17_traceSegment_092_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 607 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 607 20 21, g32p_row17_traceSegment_092_0607_0020, g32p_row17_traceSegment_092_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 567 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 567 40 41, g32p_row17_traceSegment_092_0567_0040, g32p_row17_traceSegment_092_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_092 486 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 486 81 81, g32p_row17_traceSegment_092_0486_0081, g32p_row17_traceSegment_092_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_092 324 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 324 162 162, g32p_row17_traceSegment_092_0324_0162, g32p_row17_traceSegment_092_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_092 0 648 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 0 324 324, g32p_row17_traceSegment_092_0000_0324, g32p_row17_traceSegment_092_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 648 10 10, g32p_row17_traceSegment_092_0648_0010, g32p_row17_traceSegment_092_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 668 10 10, g32p_row17_traceSegment_092_0668_0010, g32p_row17_traceSegment_092_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 648 20 20, g32p_row17_traceSegment_092_0648_0020, g32p_row17_traceSegment_092_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 688 10 10, g32p_row17_traceSegment_092_0688_0010, g32p_row17_traceSegment_092_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 708 10 11, g32p_row17_traceSegment_092_0708_0010, g32p_row17_traceSegment_092_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 688 20 21, g32p_row17_traceSegment_092_0688_0020, g32p_row17_traceSegment_092_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 648 40 41, g32p_row17_traceSegment_092_0648_0040, g32p_row17_traceSegment_092_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 739 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 729 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 729 10 10, g32p_row17_traceSegment_092_0729_0010, g32p_row17_traceSegment_092_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 749 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 749 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 749 10 10, g32p_row17_traceSegment_092_0749_0010, g32p_row17_traceSegment_092_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 729 40 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 729 20 20, g32p_row17_traceSegment_092_0729_0020, g32p_row17_traceSegment_092_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 769 10 10, g32p_row17_traceSegment_092_0769_0010, g32p_row17_traceSegment_092_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 789 10 11, g32p_row17_traceSegment_092_0789_0010, g32p_row17_traceSegment_092_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 769 20 21, g32p_row17_traceSegment_092_0769_0020, g32p_row17_traceSegment_092_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 729 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 729 40 41, g32p_row17_traceSegment_092_0729_0040, g32p_row17_traceSegment_092_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_092 648 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 648 81 81, g32p_row17_traceSegment_092_0648_0081, g32p_row17_traceSegment_092_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 810 10 10, g32p_row17_traceSegment_092_0810_0010, g32p_row17_traceSegment_092_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 830 10 10, g32p_row17_traceSegment_092_0830_0010, g32p_row17_traceSegment_092_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 810 20 20, g32p_row17_traceSegment_092_0810_0020, g32p_row17_traceSegment_092_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 850 10 10, g32p_row17_traceSegment_092_0850_0010, g32p_row17_traceSegment_092_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 870 10 11, g32p_row17_traceSegment_092_0870_0010, g32p_row17_traceSegment_092_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 850 20 21, g32p_row17_traceSegment_092_0850_0020, g32p_row17_traceSegment_092_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 810 40 41, g32p_row17_traceSegment_092_0810_0040, g32p_row17_traceSegment_092_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 891 10 10, g32p_row17_traceSegment_092_0891_0010, g32p_row17_traceSegment_092_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 911 10 10, g32p_row17_traceSegment_092_0911_0010, g32p_row17_traceSegment_092_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 891 20 20, g32p_row17_traceSegment_092_0891_0020, g32p_row17_traceSegment_092_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 931 10 10, g32p_row17_traceSegment_092_0931_0010, g32p_row17_traceSegment_092_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 951 10 11, g32p_row17_traceSegment_092_0951_0010, g32p_row17_traceSegment_092_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 931 20 21, g32p_row17_traceSegment_092_0931_0020, g32p_row17_traceSegment_092_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 891 40 41, g32p_row17_traceSegment_092_0891_0040, g32p_row17_traceSegment_092_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_092 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 810 81 81, g32p_row17_traceSegment_092_0810_0081, g32p_row17_traceSegment_092_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_092 648 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 648 162 162, g32p_row17_traceSegment_092_0648_0162, g32p_row17_traceSegment_092_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 972 10 10, g32p_row17_traceSegment_092_0972_0010, g32p_row17_traceSegment_092_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 992 10 10, g32p_row17_traceSegment_092_0992_0010, g32p_row17_traceSegment_092_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 972 20 20, g32p_row17_traceSegment_092_0972_0020, g32p_row17_traceSegment_092_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1012 10 10, g32p_row17_traceSegment_092_1012_0010, g32p_row17_traceSegment_092_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1032 10 11, g32p_row17_traceSegment_092_1032_0010, g32p_row17_traceSegment_092_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1012 20 21, g32p_row17_traceSegment_092_1012_0020, g32p_row17_traceSegment_092_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 972 40 41, g32p_row17_traceSegment_092_0972_0040, g32p_row17_traceSegment_092_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1053 10 10, g32p_row17_traceSegment_092_1053_0010, g32p_row17_traceSegment_092_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1073 10 10, g32p_row17_traceSegment_092_1073_0010, g32p_row17_traceSegment_092_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1053 20 20, g32p_row17_traceSegment_092_1053_0020, g32p_row17_traceSegment_092_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1093 10 10, g32p_row17_traceSegment_092_1093_0010, g32p_row17_traceSegment_092_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1113 10 11, g32p_row17_traceSegment_092_1113_0010, g32p_row17_traceSegment_092_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1093 20 21, g32p_row17_traceSegment_092_1093_0020, g32p_row17_traceSegment_092_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1053 40 41, g32p_row17_traceSegment_092_1053_0040, g32p_row17_traceSegment_092_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_092 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 972 81 81, g32p_row17_traceSegment_092_0972_0081, g32p_row17_traceSegment_092_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1134 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 1134 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1134 10 10, g32p_row17_traceSegment_092_1134_0010, g32p_row17_traceSegment_092_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1154 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 1154 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1154 10 10, g32p_row17_traceSegment_092_1154_0010, g32p_row17_traceSegment_092_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 1134 40 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1134 20 20, g32p_row17_traceSegment_092_1134_0020, g32p_row17_traceSegment_092_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1174 10 10, g32p_row17_traceSegment_092_1174_0010, g32p_row17_traceSegment_092_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1194 10 11, g32p_row17_traceSegment_092_1194_0010, g32p_row17_traceSegment_092_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1174 20 21, g32p_row17_traceSegment_092_1174_0020, g32p_row17_traceSegment_092_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 1134 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1134 40 41, g32p_row17_traceSegment_092_1134_0040, g32p_row17_traceSegment_092_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1215 10 10, g32p_row17_traceSegment_092_1215_0010, g32p_row17_traceSegment_092_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1235 10 10, g32p_row17_traceSegment_092_1235_0010, g32p_row17_traceSegment_092_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_092 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1215 20 20, g32p_row17_traceSegment_092_1215_0020, g32p_row17_traceSegment_092_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_092 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1255 10 10, g32p_row17_traceSegment_092_1255_0010, g32p_row17_traceSegment_092_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_092 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_092 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_092_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_092 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1275 10 11, g32p_row17_traceSegment_092_1275_0010, g32p_row17_traceSegment_092_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_092 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1255 20 21, g32p_row17_traceSegment_092_1255_0020, g32p_row17_traceSegment_092_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_092 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1215 40 41, g32p_row17_traceSegment_092_1215_0040, g32p_row17_traceSegment_092_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_092_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_092 1134 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 1134 81 81, g32p_row17_traceSegment_092_1134_0081, g32p_row17_traceSegment_092_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_092 972 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 972 162 162, g32p_row17_traceSegment_092_0972_0162, g32p_row17_traceSegment_092_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_092 648 648 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 648 324 324, g32p_row17_traceSegment_092_0648_0324, g32p_row17_traceSegment_092_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_092_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_092 0 1296 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_092 0 648 648, g32p_row17_traceSegment_092_0000_0648, g32p_row17_traceSegment_092_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 92 = [0, 0, 0, 0, 6] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_092_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_093 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 93 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_093_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 0 10 10, g32p_row17_traceSegment_093_0000_0010, g32p_row17_traceSegment_093_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 20 10 10, g32p_row17_traceSegment_093_0020_0010, g32p_row17_traceSegment_093_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 0 20 20, g32p_row17_traceSegment_093_0000_0020, g32p_row17_traceSegment_093_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 40 10 10, g32p_row17_traceSegment_093_0040_0010, g32p_row17_traceSegment_093_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 60 10 11, g32p_row17_traceSegment_093_0060_0010, g32p_row17_traceSegment_093_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 40 20 21, g32p_row17_traceSegment_093_0040_0020, g32p_row17_traceSegment_093_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 0 40 41, g32p_row17_traceSegment_093_0000_0040, g32p_row17_traceSegment_093_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 81 10 10, g32p_row17_traceSegment_093_0081_0010, g32p_row17_traceSegment_093_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 101 10 10, g32p_row17_traceSegment_093_0101_0010, g32p_row17_traceSegment_093_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 81 20 20, g32p_row17_traceSegment_093_0081_0020, g32p_row17_traceSegment_093_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 121 10 10, g32p_row17_traceSegment_093_0121_0010, g32p_row17_traceSegment_093_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 141 10 11, g32p_row17_traceSegment_093_0141_0010, g32p_row17_traceSegment_093_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 121 20 21, g32p_row17_traceSegment_093_0121_0020, g32p_row17_traceSegment_093_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 81 40 41, g32p_row17_traceSegment_093_0081_0040, g32p_row17_traceSegment_093_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_093 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 0 81 81, g32p_row17_traceSegment_093_0000_0081, g32p_row17_traceSegment_093_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 162 10 10, g32p_row17_traceSegment_093_0162_0010, g32p_row17_traceSegment_093_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 182 10 10, g32p_row17_traceSegment_093_0182_0010, g32p_row17_traceSegment_093_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 162 20 20, g32p_row17_traceSegment_093_0162_0020, g32p_row17_traceSegment_093_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 202 10 10, g32p_row17_traceSegment_093_0202_0010, g32p_row17_traceSegment_093_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 222 10 11, g32p_row17_traceSegment_093_0222_0010, g32p_row17_traceSegment_093_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 202 20 21, g32p_row17_traceSegment_093_0202_0020, g32p_row17_traceSegment_093_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 162 40 41, g32p_row17_traceSegment_093_0162_0040, g32p_row17_traceSegment_093_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 243 10 10, g32p_row17_traceSegment_093_0243_0010, g32p_row17_traceSegment_093_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 263 10 10, g32p_row17_traceSegment_093_0263_0010, g32p_row17_traceSegment_093_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 243 20 20, g32p_row17_traceSegment_093_0243_0020, g32p_row17_traceSegment_093_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 283 10 10, g32p_row17_traceSegment_093_0283_0010, g32p_row17_traceSegment_093_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 303 10 11, g32p_row17_traceSegment_093_0303_0010, g32p_row17_traceSegment_093_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 283 20 21, g32p_row17_traceSegment_093_0283_0020, g32p_row17_traceSegment_093_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 243 40 41, g32p_row17_traceSegment_093_0243_0040, g32p_row17_traceSegment_093_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_093 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 162 81 81, g32p_row17_traceSegment_093_0162_0081, g32p_row17_traceSegment_093_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_093 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 0 162 162, g32p_row17_traceSegment_093_0000_0162, g32p_row17_traceSegment_093_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 324 10 10, g32p_row17_traceSegment_093_0324_0010, g32p_row17_traceSegment_093_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 344 10 10, g32p_row17_traceSegment_093_0344_0010, g32p_row17_traceSegment_093_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 324 20 20, g32p_row17_traceSegment_093_0324_0020, g32p_row17_traceSegment_093_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 364 10 10, g32p_row17_traceSegment_093_0364_0010, g32p_row17_traceSegment_093_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 384 10 11, g32p_row17_traceSegment_093_0384_0010, g32p_row17_traceSegment_093_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 364 20 21, g32p_row17_traceSegment_093_0364_0020, g32p_row17_traceSegment_093_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 324 40 41, g32p_row17_traceSegment_093_0324_0040, g32p_row17_traceSegment_093_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 405 10 10, g32p_row17_traceSegment_093_0405_0010, g32p_row17_traceSegment_093_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 425 10 10, g32p_row17_traceSegment_093_0425_0010, g32p_row17_traceSegment_093_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 405 20 20, g32p_row17_traceSegment_093_0405_0020, g32p_row17_traceSegment_093_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 445 10 10, g32p_row17_traceSegment_093_0445_0010, g32p_row17_traceSegment_093_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 465 10 11, g32p_row17_traceSegment_093_0465_0010, g32p_row17_traceSegment_093_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 445 20 21, g32p_row17_traceSegment_093_0445_0020, g32p_row17_traceSegment_093_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 405 40 41, g32p_row17_traceSegment_093_0405_0040, g32p_row17_traceSegment_093_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_093 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 324 81 81, g32p_row17_traceSegment_093_0324_0081, g32p_row17_traceSegment_093_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 486 10 10, g32p_row17_traceSegment_093_0486_0010, g32p_row17_traceSegment_093_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 506 10 10, g32p_row17_traceSegment_093_0506_0010, g32p_row17_traceSegment_093_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 486 20 20, g32p_row17_traceSegment_093_0486_0020, g32p_row17_traceSegment_093_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 526 10 10, g32p_row17_traceSegment_093_0526_0010, g32p_row17_traceSegment_093_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 546 10 11, g32p_row17_traceSegment_093_0546_0010, g32p_row17_traceSegment_093_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 526 20 21, g32p_row17_traceSegment_093_0526_0020, g32p_row17_traceSegment_093_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 486 40 41, g32p_row17_traceSegment_093_0486_0040, g32p_row17_traceSegment_093_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 567 10 10, g32p_row17_traceSegment_093_0567_0010, g32p_row17_traceSegment_093_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 587 10 10, g32p_row17_traceSegment_093_0587_0010, g32p_row17_traceSegment_093_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 567 20 20, g32p_row17_traceSegment_093_0567_0020, g32p_row17_traceSegment_093_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 607 10 10, g32p_row17_traceSegment_093_0607_0010, g32p_row17_traceSegment_093_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 627 10 11, g32p_row17_traceSegment_093_0627_0010, g32p_row17_traceSegment_093_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 607 20 21, g32p_row17_traceSegment_093_0607_0020, g32p_row17_traceSegment_093_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 567 40 41, g32p_row17_traceSegment_093_0567_0040, g32p_row17_traceSegment_093_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_093 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 486 81 81, g32p_row17_traceSegment_093_0486_0081, g32p_row17_traceSegment_093_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_093 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 324 162 162, g32p_row17_traceSegment_093_0324_0162, g32p_row17_traceSegment_093_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_093 0 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 0 324 324, g32p_row17_traceSegment_093_0000_0324, g32p_row17_traceSegment_093_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 648 10 10, g32p_row17_traceSegment_093_0648_0010, g32p_row17_traceSegment_093_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 668 10 10, g32p_row17_traceSegment_093_0668_0010, g32p_row17_traceSegment_093_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 648 20 20, g32p_row17_traceSegment_093_0648_0020, g32p_row17_traceSegment_093_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 688 10 10, g32p_row17_traceSegment_093_0688_0010, g32p_row17_traceSegment_093_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 708 10 11, g32p_row17_traceSegment_093_0708_0010, g32p_row17_traceSegment_093_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 688 20 21, g32p_row17_traceSegment_093_0688_0020, g32p_row17_traceSegment_093_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 648 40 41, g32p_row17_traceSegment_093_0648_0040, g32p_row17_traceSegment_093_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 729 10 10, g32p_row17_traceSegment_093_0729_0010, g32p_row17_traceSegment_093_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 749 10 10, g32p_row17_traceSegment_093_0749_0010, g32p_row17_traceSegment_093_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 729 20 20, g32p_row17_traceSegment_093_0729_0020, g32p_row17_traceSegment_093_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 769 10 10, g32p_row17_traceSegment_093_0769_0010, g32p_row17_traceSegment_093_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 789 10 11, g32p_row17_traceSegment_093_0789_0010, g32p_row17_traceSegment_093_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 769 20 21, g32p_row17_traceSegment_093_0769_0020, g32p_row17_traceSegment_093_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 729 40 41, g32p_row17_traceSegment_093_0729_0040, g32p_row17_traceSegment_093_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_093 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 648 81 81, g32p_row17_traceSegment_093_0648_0081, g32p_row17_traceSegment_093_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 810 10 10, g32p_row17_traceSegment_093_0810_0010, g32p_row17_traceSegment_093_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 830 10 10, g32p_row17_traceSegment_093_0830_0010, g32p_row17_traceSegment_093_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 810 20 20, g32p_row17_traceSegment_093_0810_0020, g32p_row17_traceSegment_093_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 850 10 10, g32p_row17_traceSegment_093_0850_0010, g32p_row17_traceSegment_093_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 870 10 11, g32p_row17_traceSegment_093_0870_0010, g32p_row17_traceSegment_093_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 850 20 21, g32p_row17_traceSegment_093_0850_0020, g32p_row17_traceSegment_093_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 810 40 41, g32p_row17_traceSegment_093_0810_0040, g32p_row17_traceSegment_093_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 891 10 10, g32p_row17_traceSegment_093_0891_0010, g32p_row17_traceSegment_093_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 911 10 10, g32p_row17_traceSegment_093_0911_0010, g32p_row17_traceSegment_093_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 891 20 20, g32p_row17_traceSegment_093_0891_0020, g32p_row17_traceSegment_093_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 931 10 10, g32p_row17_traceSegment_093_0931_0010, g32p_row17_traceSegment_093_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 951 10 11, g32p_row17_traceSegment_093_0951_0010, g32p_row17_traceSegment_093_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 931 20 21, g32p_row17_traceSegment_093_0931_0020, g32p_row17_traceSegment_093_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 891 40 41, g32p_row17_traceSegment_093_0891_0040, g32p_row17_traceSegment_093_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_093 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 810 81 81, g32p_row17_traceSegment_093_0810_0081, g32p_row17_traceSegment_093_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_093 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 648 162 162, g32p_row17_traceSegment_093_0648_0162, g32p_row17_traceSegment_093_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 972 10 10, g32p_row17_traceSegment_093_0972_0010, g32p_row17_traceSegment_093_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 992 10 10, g32p_row17_traceSegment_093_0992_0010, g32p_row17_traceSegment_093_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 972 20 20, g32p_row17_traceSegment_093_0972_0020, g32p_row17_traceSegment_093_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1012 10 10, g32p_row17_traceSegment_093_1012_0010, g32p_row17_traceSegment_093_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1032 10 11, g32p_row17_traceSegment_093_1032_0010, g32p_row17_traceSegment_093_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1012 20 21, g32p_row17_traceSegment_093_1012_0020, g32p_row17_traceSegment_093_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 972 40 41, g32p_row17_traceSegment_093_0972_0040, g32p_row17_traceSegment_093_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1053 10 10, g32p_row17_traceSegment_093_1053_0010, g32p_row17_traceSegment_093_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1073 10 10, g32p_row17_traceSegment_093_1073_0010, g32p_row17_traceSegment_093_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1053 20 20, g32p_row17_traceSegment_093_1053_0020, g32p_row17_traceSegment_093_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1103 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 1093 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1093 10 10, g32p_row17_traceSegment_093_1093_0010, g32p_row17_traceSegment_093_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 1123 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 1113 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1113 10 11, g32p_row17_traceSegment_093_1113_0010, g32p_row17_traceSegment_093_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 1093 41 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1093 20 21, g32p_row17_traceSegment_093_1093_0020, g32p_row17_traceSegment_093_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 1053 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1053 40 41, g32p_row17_traceSegment_093_1053_0040, g32p_row17_traceSegment_093_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_093 972 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 972 81 81, g32p_row17_traceSegment_093_0972_0081, g32p_row17_traceSegment_093_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1134 10 10, g32p_row17_traceSegment_093_1134_0010, g32p_row17_traceSegment_093_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1154 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 1154 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1154 10 10, g32p_row17_traceSegment_093_1154_0010, g32p_row17_traceSegment_093_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 1134 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1134 20 20, g32p_row17_traceSegment_093_1134_0020, g32p_row17_traceSegment_093_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1184 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 1174 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1174 10 10, g32p_row17_traceSegment_093_1174_0010, g32p_row17_traceSegment_093_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1194 10 11, g32p_row17_traceSegment_093_1194_0010, g32p_row17_traceSegment_093_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 1174 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1174 20 21, g32p_row17_traceSegment_093_1174_0020, g32p_row17_traceSegment_093_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 1134 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1134 40 41, g32p_row17_traceSegment_093_1134_0040, g32p_row17_traceSegment_093_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1215 10 10, g32p_row17_traceSegment_093_1215_0010, g32p_row17_traceSegment_093_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1235 10 10, g32p_row17_traceSegment_093_1235_0010, g32p_row17_traceSegment_093_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_093 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1215 20 20, g32p_row17_traceSegment_093_1215_0020, g32p_row17_traceSegment_093_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_093 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1255 10 10, g32p_row17_traceSegment_093_1255_0010, g32p_row17_traceSegment_093_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_093 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_093 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_093_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_093 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1275 10 11, g32p_row17_traceSegment_093_1275_0010, g32p_row17_traceSegment_093_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_093 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1255 20 21, g32p_row17_traceSegment_093_1255_0020, g32p_row17_traceSegment_093_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_093 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1215 40 41, g32p_row17_traceSegment_093_1215_0040, g32p_row17_traceSegment_093_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_093_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_093 1134 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 1134 81 81, g32p_row17_traceSegment_093_1134_0081, g32p_row17_traceSegment_093_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_093 972 324 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 972 162 162, g32p_row17_traceSegment_093_0972_0162, g32p_row17_traceSegment_093_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_093 648 648 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 648 324 324, g32p_row17_traceSegment_093_0648_0324, g32p_row17_traceSegment_093_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_093_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_093 0 1296 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_093 0 648 648, g32p_row17_traceSegment_093_0000_0648, g32p_row17_traceSegment_093_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 93 = [0, 0, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_093_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_095 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 95 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_095_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 0 10 10, g32p_row17_traceSegment_095_0000_0010, g32p_row17_traceSegment_095_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 20 10 10, g32p_row17_traceSegment_095_0020_0010, g32p_row17_traceSegment_095_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 0 20 20, g32p_row17_traceSegment_095_0000_0020, g32p_row17_traceSegment_095_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 40 10 10, g32p_row17_traceSegment_095_0040_0010, g32p_row17_traceSegment_095_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 60 10 11, g32p_row17_traceSegment_095_0060_0010, g32p_row17_traceSegment_095_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 40 20 21, g32p_row17_traceSegment_095_0040_0020, g32p_row17_traceSegment_095_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 0 40 41, g32p_row17_traceSegment_095_0000_0040, g32p_row17_traceSegment_095_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 81 10 10, g32p_row17_traceSegment_095_0081_0010, g32p_row17_traceSegment_095_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 101 10 10, g32p_row17_traceSegment_095_0101_0010, g32p_row17_traceSegment_095_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 81 20 20, g32p_row17_traceSegment_095_0081_0020, g32p_row17_traceSegment_095_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 121 10 10, g32p_row17_traceSegment_095_0121_0010, g32p_row17_traceSegment_095_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 141 10 11, g32p_row17_traceSegment_095_0141_0010, g32p_row17_traceSegment_095_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 121 20 21, g32p_row17_traceSegment_095_0121_0020, g32p_row17_traceSegment_095_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 81 40 41, g32p_row17_traceSegment_095_0081_0040, g32p_row17_traceSegment_095_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_095 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 0 81 81, g32p_row17_traceSegment_095_0000_0081, g32p_row17_traceSegment_095_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 162 10 10, g32p_row17_traceSegment_095_0162_0010, g32p_row17_traceSegment_095_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 182 10 10, g32p_row17_traceSegment_095_0182_0010, g32p_row17_traceSegment_095_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 162 20 20, g32p_row17_traceSegment_095_0162_0020, g32p_row17_traceSegment_095_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 202 10 10, g32p_row17_traceSegment_095_0202_0010, g32p_row17_traceSegment_095_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 222 10 11, g32p_row17_traceSegment_095_0222_0010, g32p_row17_traceSegment_095_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 202 20 21, g32p_row17_traceSegment_095_0202_0020, g32p_row17_traceSegment_095_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 162 40 41, g32p_row17_traceSegment_095_0162_0040, g32p_row17_traceSegment_095_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 243 10 10, g32p_row17_traceSegment_095_0243_0010, g32p_row17_traceSegment_095_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 263 10 10, g32p_row17_traceSegment_095_0263_0010, g32p_row17_traceSegment_095_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 243 20 20, g32p_row17_traceSegment_095_0243_0020, g32p_row17_traceSegment_095_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 283 10 10, g32p_row17_traceSegment_095_0283_0010, g32p_row17_traceSegment_095_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 303 10 11, g32p_row17_traceSegment_095_0303_0010, g32p_row17_traceSegment_095_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 283 20 21, g32p_row17_traceSegment_095_0283_0020, g32p_row17_traceSegment_095_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 243 40 41, g32p_row17_traceSegment_095_0243_0040, g32p_row17_traceSegment_095_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_095 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 162 81 81, g32p_row17_traceSegment_095_0162_0081, g32p_row17_traceSegment_095_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_095 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 0 162 162, g32p_row17_traceSegment_095_0000_0162, g32p_row17_traceSegment_095_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 324 10 10, g32p_row17_traceSegment_095_0324_0010, g32p_row17_traceSegment_095_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 344 10 10, g32p_row17_traceSegment_095_0344_0010, g32p_row17_traceSegment_095_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 324 20 20, g32p_row17_traceSegment_095_0324_0020, g32p_row17_traceSegment_095_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 364 10 10, g32p_row17_traceSegment_095_0364_0010, g32p_row17_traceSegment_095_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 384 10 11, g32p_row17_traceSegment_095_0384_0010, g32p_row17_traceSegment_095_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 364 20 21, g32p_row17_traceSegment_095_0364_0020, g32p_row17_traceSegment_095_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 324 40 41, g32p_row17_traceSegment_095_0324_0040, g32p_row17_traceSegment_095_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 405 10 10, g32p_row17_traceSegment_095_0405_0010, g32p_row17_traceSegment_095_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 425 10 10, g32p_row17_traceSegment_095_0425_0010, g32p_row17_traceSegment_095_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 405 20 20, g32p_row17_traceSegment_095_0405_0020, g32p_row17_traceSegment_095_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 445 10 10, g32p_row17_traceSegment_095_0445_0010, g32p_row17_traceSegment_095_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 465 10 11, g32p_row17_traceSegment_095_0465_0010, g32p_row17_traceSegment_095_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 445 20 21, g32p_row17_traceSegment_095_0445_0020, g32p_row17_traceSegment_095_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 405 40 41, g32p_row17_traceSegment_095_0405_0040, g32p_row17_traceSegment_095_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_095 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 324 81 81, g32p_row17_traceSegment_095_0324_0081, g32p_row17_traceSegment_095_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 486 10 10, g32p_row17_traceSegment_095_0486_0010, g32p_row17_traceSegment_095_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 506 10 10, g32p_row17_traceSegment_095_0506_0010, g32p_row17_traceSegment_095_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 486 20 20, g32p_row17_traceSegment_095_0486_0020, g32p_row17_traceSegment_095_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 526 10 10, g32p_row17_traceSegment_095_0526_0010, g32p_row17_traceSegment_095_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 546 10 11, g32p_row17_traceSegment_095_0546_0010, g32p_row17_traceSegment_095_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 526 20 21, g32p_row17_traceSegment_095_0526_0020, g32p_row17_traceSegment_095_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 486 40 41, g32p_row17_traceSegment_095_0486_0040, g32p_row17_traceSegment_095_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 567 10 10, g32p_row17_traceSegment_095_0567_0010, g32p_row17_traceSegment_095_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 587 10 10, g32p_row17_traceSegment_095_0587_0010, g32p_row17_traceSegment_095_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 567 20 20, g32p_row17_traceSegment_095_0567_0020, g32p_row17_traceSegment_095_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 607 10 10, g32p_row17_traceSegment_095_0607_0010, g32p_row17_traceSegment_095_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 627 10 11, g32p_row17_traceSegment_095_0627_0010, g32p_row17_traceSegment_095_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 607 20 21, g32p_row17_traceSegment_095_0607_0020, g32p_row17_traceSegment_095_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 567 40 41, g32p_row17_traceSegment_095_0567_0040, g32p_row17_traceSegment_095_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_095 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 486 81 81, g32p_row17_traceSegment_095_0486_0081, g32p_row17_traceSegment_095_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_095 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 324 162 162, g32p_row17_traceSegment_095_0324_0162, g32p_row17_traceSegment_095_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_095 0 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 0 324 324, g32p_row17_traceSegment_095_0000_0324, g32p_row17_traceSegment_095_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 648 10 10, g32p_row17_traceSegment_095_0648_0010, g32p_row17_traceSegment_095_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 668 10 10, g32p_row17_traceSegment_095_0668_0010, g32p_row17_traceSegment_095_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 648 20 20, g32p_row17_traceSegment_095_0648_0020, g32p_row17_traceSegment_095_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 688 10 10, g32p_row17_traceSegment_095_0688_0010, g32p_row17_traceSegment_095_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 708 10 11, g32p_row17_traceSegment_095_0708_0010, g32p_row17_traceSegment_095_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 688 20 21, g32p_row17_traceSegment_095_0688_0020, g32p_row17_traceSegment_095_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 648 40 41, g32p_row17_traceSegment_095_0648_0040, g32p_row17_traceSegment_095_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 729 10 10, g32p_row17_traceSegment_095_0729_0010, g32p_row17_traceSegment_095_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 749 10 10, g32p_row17_traceSegment_095_0749_0010, g32p_row17_traceSegment_095_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 729 20 20, g32p_row17_traceSegment_095_0729_0020, g32p_row17_traceSegment_095_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 769 10 10, g32p_row17_traceSegment_095_0769_0010, g32p_row17_traceSegment_095_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 789 10 11, g32p_row17_traceSegment_095_0789_0010, g32p_row17_traceSegment_095_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 769 20 21, g32p_row17_traceSegment_095_0769_0020, g32p_row17_traceSegment_095_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 729 40 41, g32p_row17_traceSegment_095_0729_0040, g32p_row17_traceSegment_095_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_095 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 648 81 81, g32p_row17_traceSegment_095_0648_0081, g32p_row17_traceSegment_095_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 810 10 10, g32p_row17_traceSegment_095_0810_0010, g32p_row17_traceSegment_095_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 830 10 10, g32p_row17_traceSegment_095_0830_0010, g32p_row17_traceSegment_095_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 810 20 20, g32p_row17_traceSegment_095_0810_0020, g32p_row17_traceSegment_095_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 850 10 10, g32p_row17_traceSegment_095_0850_0010, g32p_row17_traceSegment_095_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 870 10 11, g32p_row17_traceSegment_095_0870_0010, g32p_row17_traceSegment_095_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 850 20 21, g32p_row17_traceSegment_095_0850_0020, g32p_row17_traceSegment_095_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 810 40 41, g32p_row17_traceSegment_095_0810_0040, g32p_row17_traceSegment_095_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 891 10 10, g32p_row17_traceSegment_095_0891_0010, g32p_row17_traceSegment_095_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 911 10 10, g32p_row17_traceSegment_095_0911_0010, g32p_row17_traceSegment_095_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 891 20 20, g32p_row17_traceSegment_095_0891_0020, g32p_row17_traceSegment_095_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 931 10 10, g32p_row17_traceSegment_095_0931_0010, g32p_row17_traceSegment_095_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 951 10 11, g32p_row17_traceSegment_095_0951_0010, g32p_row17_traceSegment_095_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 931 20 21, g32p_row17_traceSegment_095_0931_0020, g32p_row17_traceSegment_095_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 891 40 41, g32p_row17_traceSegment_095_0891_0040, g32p_row17_traceSegment_095_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_095 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 810 81 81, g32p_row17_traceSegment_095_0810_0081, g32p_row17_traceSegment_095_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_095 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 648 162 162, g32p_row17_traceSegment_095_0648_0162, g32p_row17_traceSegment_095_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 972 10 10, g32p_row17_traceSegment_095_0972_0010, g32p_row17_traceSegment_095_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 992 10 10, g32p_row17_traceSegment_095_0992_0010, g32p_row17_traceSegment_095_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 972 20 20, g32p_row17_traceSegment_095_0972_0020, g32p_row17_traceSegment_095_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1012 10 10, g32p_row17_traceSegment_095_1012_0010, g32p_row17_traceSegment_095_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1032 10 11, g32p_row17_traceSegment_095_1032_0010, g32p_row17_traceSegment_095_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1012 20 21, g32p_row17_traceSegment_095_1012_0020, g32p_row17_traceSegment_095_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 972 40 41, g32p_row17_traceSegment_095_0972_0040, g32p_row17_traceSegment_095_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1053 10 10, g32p_row17_traceSegment_095_1053_0010, g32p_row17_traceSegment_095_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1073 10 10, g32p_row17_traceSegment_095_1073_0010, g32p_row17_traceSegment_095_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1053 20 20, g32p_row17_traceSegment_095_1053_0020, g32p_row17_traceSegment_095_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1093 10 10, g32p_row17_traceSegment_095_1093_0010, g32p_row17_traceSegment_095_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1113 10 11, g32p_row17_traceSegment_095_1113_0010, g32p_row17_traceSegment_095_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1093 20 21, g32p_row17_traceSegment_095_1093_0020, g32p_row17_traceSegment_095_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1053 40 41, g32p_row17_traceSegment_095_1053_0040, g32p_row17_traceSegment_095_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_095 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 972 81 81, g32p_row17_traceSegment_095_0972_0081, g32p_row17_traceSegment_095_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1134 10 10, g32p_row17_traceSegment_095_1134_0010, g32p_row17_traceSegment_095_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1154 10 10, g32p_row17_traceSegment_095_1154_0010, g32p_row17_traceSegment_095_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1134 20 20, g32p_row17_traceSegment_095_1134_0020, g32p_row17_traceSegment_095_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1174 10 10, g32p_row17_traceSegment_095_1174_0010, g32p_row17_traceSegment_095_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1194 10 11, g32p_row17_traceSegment_095_1194_0010, g32p_row17_traceSegment_095_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1174 20 21, g32p_row17_traceSegment_095_1174_0020, g32p_row17_traceSegment_095_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1134 40 41, g32p_row17_traceSegment_095_1134_0040, g32p_row17_traceSegment_095_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1215 10 10, g32p_row17_traceSegment_095_1215_0010, g32p_row17_traceSegment_095_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1235 10 10, g32p_row17_traceSegment_095_1235_0010, g32p_row17_traceSegment_095_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_095 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1215 20 20, g32p_row17_traceSegment_095_1215_0020, g32p_row17_traceSegment_095_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_095 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1255 10 10, g32p_row17_traceSegment_095_1255_0010, g32p_row17_traceSegment_095_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_095 1275 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_095 1285 11 = [3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_095_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_095 1275 21 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1275 10 11, g32p_row17_traceSegment_095_1275_0010, g32p_row17_traceSegment_095_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_095 1255 41 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1255 20 21, g32p_row17_traceSegment_095_1255_0020, g32p_row17_traceSegment_095_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_095 1215 81 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1215 40 41, g32p_row17_traceSegment_095_1215_0040, g32p_row17_traceSegment_095_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_095_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_095 1134 162 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 1134 81 81, g32p_row17_traceSegment_095_1134_0081, g32p_row17_traceSegment_095_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_095 972 324 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 972 162 162, g32p_row17_traceSegment_095_0972_0162, g32p_row17_traceSegment_095_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_095 648 648 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 648 324 324, g32p_row17_traceSegment_095_0648_0324, g32p_row17_traceSegment_095_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_095_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_095 0 1296 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_095 0 648 648, g32p_row17_traceSegment_095_0000_0648, g32p_row17_traceSegment_095_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 95 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_095_0000_1296

end HodgeLean.Foundations.Program

end
end
