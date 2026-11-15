import HodgeLean.Foundations.Program.G32PropFourSixPacked0367
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0371

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_074 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 74 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_074_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 0 10 10, g32p_row17_traceSegment_074_0000_0010, g32p_row17_traceSegment_074_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 20 10 10, g32p_row17_traceSegment_074_0020_0010, g32p_row17_traceSegment_074_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 0 20 20, g32p_row17_traceSegment_074_0000_0020, g32p_row17_traceSegment_074_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 40 10 10, g32p_row17_traceSegment_074_0040_0010, g32p_row17_traceSegment_074_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 60 10 11, g32p_row17_traceSegment_074_0060_0010, g32p_row17_traceSegment_074_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 40 20 21, g32p_row17_traceSegment_074_0040_0020, g32p_row17_traceSegment_074_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 0 40 41, g32p_row17_traceSegment_074_0000_0040, g32p_row17_traceSegment_074_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 81 10 10, g32p_row17_traceSegment_074_0081_0010, g32p_row17_traceSegment_074_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 101 10 10, g32p_row17_traceSegment_074_0101_0010, g32p_row17_traceSegment_074_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 81 20 20, g32p_row17_traceSegment_074_0081_0020, g32p_row17_traceSegment_074_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 121 10 10, g32p_row17_traceSegment_074_0121_0010, g32p_row17_traceSegment_074_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 141 10 11, g32p_row17_traceSegment_074_0141_0010, g32p_row17_traceSegment_074_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 121 20 21, g32p_row17_traceSegment_074_0121_0020, g32p_row17_traceSegment_074_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 81 40 41, g32p_row17_traceSegment_074_0081_0040, g32p_row17_traceSegment_074_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_074 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 0 81 81, g32p_row17_traceSegment_074_0000_0081, g32p_row17_traceSegment_074_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 162 10 10, g32p_row17_traceSegment_074_0162_0010, g32p_row17_traceSegment_074_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 182 10 10, g32p_row17_traceSegment_074_0182_0010, g32p_row17_traceSegment_074_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 162 20 20, g32p_row17_traceSegment_074_0162_0020, g32p_row17_traceSegment_074_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 202 10 10, g32p_row17_traceSegment_074_0202_0010, g32p_row17_traceSegment_074_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 232 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 222 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 222 10 11, g32p_row17_traceSegment_074_0222_0010, g32p_row17_traceSegment_074_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 202 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 202 20 21, g32p_row17_traceSegment_074_0202_0020, g32p_row17_traceSegment_074_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 162 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 162 40 41, g32p_row17_traceSegment_074_0162_0040, g32p_row17_traceSegment_074_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 243 10 10, g32p_row17_traceSegment_074_0243_0010, g32p_row17_traceSegment_074_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 263 10 10, g32p_row17_traceSegment_074_0263_0010, g32p_row17_traceSegment_074_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 243 20 20, g32p_row17_traceSegment_074_0243_0020, g32p_row17_traceSegment_074_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 293 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 283 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 283 10 10, g32p_row17_traceSegment_074_0283_0010, g32p_row17_traceSegment_074_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 303 10 11, g32p_row17_traceSegment_074_0303_0010, g32p_row17_traceSegment_074_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 283 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 283 20 21, g32p_row17_traceSegment_074_0283_0020, g32p_row17_traceSegment_074_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 243 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 243 40 41, g32p_row17_traceSegment_074_0243_0040, g32p_row17_traceSegment_074_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_074 162 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 162 81 81, g32p_row17_traceSegment_074_0162_0081, g32p_row17_traceSegment_074_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_074 0 324 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 0 162 162, g32p_row17_traceSegment_074_0000_0162, g32p_row17_traceSegment_074_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 324 10 10, g32p_row17_traceSegment_074_0324_0010, g32p_row17_traceSegment_074_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 344 10 10, g32p_row17_traceSegment_074_0344_0010, g32p_row17_traceSegment_074_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 324 20 20, g32p_row17_traceSegment_074_0324_0020, g32p_row17_traceSegment_074_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 374 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 364 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 364 10 10, g32p_row17_traceSegment_074_0364_0010, g32p_row17_traceSegment_074_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 394 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 384 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 384 10 11, g32p_row17_traceSegment_074_0384_0010, g32p_row17_traceSegment_074_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 364 41 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 364 20 21, g32p_row17_traceSegment_074_0364_0020, g32p_row17_traceSegment_074_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 324 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 324 40 41, g32p_row17_traceSegment_074_0324_0040, g32p_row17_traceSegment_074_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 415 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 405 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 405 10 10, g32p_row17_traceSegment_074_0405_0010, g32p_row17_traceSegment_074_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 425 10 10, g32p_row17_traceSegment_074_0425_0010, g32p_row17_traceSegment_074_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 405 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 405 20 20, g32p_row17_traceSegment_074_0405_0020, g32p_row17_traceSegment_074_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 445 10 10, g32p_row17_traceSegment_074_0445_0010, g32p_row17_traceSegment_074_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 465 10 11, g32p_row17_traceSegment_074_0465_0010, g32p_row17_traceSegment_074_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 445 20 21, g32p_row17_traceSegment_074_0445_0020, g32p_row17_traceSegment_074_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 405 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 405 40 41, g32p_row17_traceSegment_074_0405_0040, g32p_row17_traceSegment_074_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_074 324 162 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 324 81 81, g32p_row17_traceSegment_074_0324_0081, g32p_row17_traceSegment_074_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 486 10 10, g32p_row17_traceSegment_074_0486_0010, g32p_row17_traceSegment_074_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 506 10 10, g32p_row17_traceSegment_074_0506_0010, g32p_row17_traceSegment_074_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 486 20 20, g32p_row17_traceSegment_074_0486_0020, g32p_row17_traceSegment_074_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 526 10 10, g32p_row17_traceSegment_074_0526_0010, g32p_row17_traceSegment_074_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 546 10 11, g32p_row17_traceSegment_074_0546_0010, g32p_row17_traceSegment_074_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 526 20 21, g32p_row17_traceSegment_074_0526_0020, g32p_row17_traceSegment_074_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 486 40 41, g32p_row17_traceSegment_074_0486_0040, g32p_row17_traceSegment_074_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 567 10 10, g32p_row17_traceSegment_074_0567_0010, g32p_row17_traceSegment_074_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 587 10 10, g32p_row17_traceSegment_074_0587_0010, g32p_row17_traceSegment_074_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 567 20 20, g32p_row17_traceSegment_074_0567_0020, g32p_row17_traceSegment_074_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 607 10 10, g32p_row17_traceSegment_074_0607_0010, g32p_row17_traceSegment_074_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 627 10 11, g32p_row17_traceSegment_074_0627_0010, g32p_row17_traceSegment_074_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 607 20 21, g32p_row17_traceSegment_074_0607_0020, g32p_row17_traceSegment_074_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 567 40 41, g32p_row17_traceSegment_074_0567_0040, g32p_row17_traceSegment_074_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_074 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 486 81 81, g32p_row17_traceSegment_074_0486_0081, g32p_row17_traceSegment_074_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_074 324 324 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 324 162 162, g32p_row17_traceSegment_074_0324_0162, g32p_row17_traceSegment_074_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_074 0 648 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 0 324 324, g32p_row17_traceSegment_074_0000_0324, g32p_row17_traceSegment_074_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 648 10 10, g32p_row17_traceSegment_074_0648_0010, g32p_row17_traceSegment_074_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 668 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 668 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 668 10 10, g32p_row17_traceSegment_074_0668_0010, g32p_row17_traceSegment_074_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 648 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 648 20 20, g32p_row17_traceSegment_074_0648_0020, g32p_row17_traceSegment_074_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 688 10 10, g32p_row17_traceSegment_074_0688_0010, g32p_row17_traceSegment_074_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 708 10 11, g32p_row17_traceSegment_074_0708_0010, g32p_row17_traceSegment_074_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 688 20 21, g32p_row17_traceSegment_074_0688_0020, g32p_row17_traceSegment_074_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 648 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 648 40 41, g32p_row17_traceSegment_074_0648_0040, g32p_row17_traceSegment_074_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 729 10 10, g32p_row17_traceSegment_074_0729_0010, g32p_row17_traceSegment_074_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 749 10 10, g32p_row17_traceSegment_074_0749_0010, g32p_row17_traceSegment_074_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 729 20 20, g32p_row17_traceSegment_074_0729_0020, g32p_row17_traceSegment_074_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 769 10 10, g32p_row17_traceSegment_074_0769_0010, g32p_row17_traceSegment_074_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 789 10 11, g32p_row17_traceSegment_074_0789_0010, g32p_row17_traceSegment_074_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 769 20 21, g32p_row17_traceSegment_074_0769_0020, g32p_row17_traceSegment_074_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 729 40 41, g32p_row17_traceSegment_074_0729_0040, g32p_row17_traceSegment_074_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_074 648 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 648 81 81, g32p_row17_traceSegment_074_0648_0081, g32p_row17_traceSegment_074_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 810 10 10, g32p_row17_traceSegment_074_0810_0010, g32p_row17_traceSegment_074_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 830 10 10, g32p_row17_traceSegment_074_0830_0010, g32p_row17_traceSegment_074_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 810 20 20, g32p_row17_traceSegment_074_0810_0020, g32p_row17_traceSegment_074_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 850 10 10, g32p_row17_traceSegment_074_0850_0010, g32p_row17_traceSegment_074_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 870 10 11, g32p_row17_traceSegment_074_0870_0010, g32p_row17_traceSegment_074_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 850 20 21, g32p_row17_traceSegment_074_0850_0020, g32p_row17_traceSegment_074_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 810 40 41, g32p_row17_traceSegment_074_0810_0040, g32p_row17_traceSegment_074_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 891 10 10, g32p_row17_traceSegment_074_0891_0010, g32p_row17_traceSegment_074_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 911 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 911 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 911 10 10, g32p_row17_traceSegment_074_0911_0010, g32p_row17_traceSegment_074_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 891 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 891 20 20, g32p_row17_traceSegment_074_0891_0020, g32p_row17_traceSegment_074_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 931 10 10, g32p_row17_traceSegment_074_0931_0010, g32p_row17_traceSegment_074_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 951 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 951 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 951 10 11, g32p_row17_traceSegment_074_0951_0010, g32p_row17_traceSegment_074_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 931 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 931 20 21, g32p_row17_traceSegment_074_0931_0020, g32p_row17_traceSegment_074_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 891 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 891 40 41, g32p_row17_traceSegment_074_0891_0040, g32p_row17_traceSegment_074_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_074 810 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 810 81 81, g32p_row17_traceSegment_074_0810_0081, g32p_row17_traceSegment_074_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_074 648 324 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 648 162 162, g32p_row17_traceSegment_074_0648_0162, g32p_row17_traceSegment_074_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 972 10 10, g32p_row17_traceSegment_074_0972_0010, g32p_row17_traceSegment_074_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 992 10 10, g32p_row17_traceSegment_074_0992_0010, g32p_row17_traceSegment_074_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 972 20 20, g32p_row17_traceSegment_074_0972_0020, g32p_row17_traceSegment_074_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1012 10 10, g32p_row17_traceSegment_074_1012_0010, g32p_row17_traceSegment_074_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1032 10 11, g32p_row17_traceSegment_074_1032_0010, g32p_row17_traceSegment_074_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1012 20 21, g32p_row17_traceSegment_074_1012_0020, g32p_row17_traceSegment_074_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 972 40 41, g32p_row17_traceSegment_074_0972_0040, g32p_row17_traceSegment_074_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1053 10 10, g32p_row17_traceSegment_074_1053_0010, g32p_row17_traceSegment_074_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1073 10 10, g32p_row17_traceSegment_074_1073_0010, g32p_row17_traceSegment_074_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1053 20 20, g32p_row17_traceSegment_074_1053_0020, g32p_row17_traceSegment_074_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1093 10 10, g32p_row17_traceSegment_074_1093_0010, g32p_row17_traceSegment_074_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 1123 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 1113 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1113 10 11, g32p_row17_traceSegment_074_1113_0010, g32p_row17_traceSegment_074_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 1093 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1093 20 21, g32p_row17_traceSegment_074_1093_0020, g32p_row17_traceSegment_074_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 1053 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1053 40 41, g32p_row17_traceSegment_074_1053_0040, g32p_row17_traceSegment_074_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_074 972 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 972 81 81, g32p_row17_traceSegment_074_0972_0081, g32p_row17_traceSegment_074_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1134 10 10, g32p_row17_traceSegment_074_1134_0010, g32p_row17_traceSegment_074_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1154 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 1154 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1154 10 10, g32p_row17_traceSegment_074_1154_0010, g32p_row17_traceSegment_074_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 1134 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1134 20 20, g32p_row17_traceSegment_074_1134_0020, g32p_row17_traceSegment_074_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1174 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 1174 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1174 10 10, g32p_row17_traceSegment_074_1174_0010, g32p_row17_traceSegment_074_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1194 10 11, g32p_row17_traceSegment_074_1194_0010, g32p_row17_traceSegment_074_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 1174 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1174 20 21, g32p_row17_traceSegment_074_1174_0020, g32p_row17_traceSegment_074_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 1134 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1134 40 41, g32p_row17_traceSegment_074_1134_0040, g32p_row17_traceSegment_074_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1225 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 1215 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1215 10 10, g32p_row17_traceSegment_074_1215_0010, g32p_row17_traceSegment_074_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1235 10 10, g32p_row17_traceSegment_074_1235_0010, g32p_row17_traceSegment_074_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_074 1215 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1215 20 20, g32p_row17_traceSegment_074_1215_0020, g32p_row17_traceSegment_074_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_074 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1255 10 10, g32p_row17_traceSegment_074_1255_0010, g32p_row17_traceSegment_074_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_074 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_074 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_074_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_074 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1275 10 11, g32p_row17_traceSegment_074_1275_0010, g32p_row17_traceSegment_074_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_074 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1255 20 21, g32p_row17_traceSegment_074_1255_0020, g32p_row17_traceSegment_074_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_074 1215 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1215 40 41, g32p_row17_traceSegment_074_1215_0040, g32p_row17_traceSegment_074_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_074_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_074 1134 162 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 1134 81 81, g32p_row17_traceSegment_074_1134_0081, g32p_row17_traceSegment_074_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_074 972 324 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 972 162 162, g32p_row17_traceSegment_074_0972_0162, g32p_row17_traceSegment_074_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_074 648 648 = [7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 648 324 324, g32p_row17_traceSegment_074_0648_0324, g32p_row17_traceSegment_074_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_074_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_074 0 1296 = [12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_074 0 648 648, g32p_row17_traceSegment_074_0000_0648, g32p_row17_traceSegment_074_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_074 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 74 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_074_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_075 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 75 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_075_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 0 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 0 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 0 10 10, g32p_row17_traceSegment_075_0000_0010, g32p_row17_traceSegment_075_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 20 10 10, g32p_row17_traceSegment_075_0020_0010, g32p_row17_traceSegment_075_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 0 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 0 20 20, g32p_row17_traceSegment_075_0000_0020, g32p_row17_traceSegment_075_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 40 10 10, g32p_row17_traceSegment_075_0040_0010, g32p_row17_traceSegment_075_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 60 10 11, g32p_row17_traceSegment_075_0060_0010, g32p_row17_traceSegment_075_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 40 20 21, g32p_row17_traceSegment_075_0040_0020, g32p_row17_traceSegment_075_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 0 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 0 40 41, g32p_row17_traceSegment_075_0000_0040, g32p_row17_traceSegment_075_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 81 10 10, g32p_row17_traceSegment_075_0081_0010, g32p_row17_traceSegment_075_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 101 10 10, g32p_row17_traceSegment_075_0101_0010, g32p_row17_traceSegment_075_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 81 20 20, g32p_row17_traceSegment_075_0081_0020, g32p_row17_traceSegment_075_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 121 10 10, g32p_row17_traceSegment_075_0121_0010, g32p_row17_traceSegment_075_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 141 10 11, g32p_row17_traceSegment_075_0141_0010, g32p_row17_traceSegment_075_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 121 20 21, g32p_row17_traceSegment_075_0121_0020, g32p_row17_traceSegment_075_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 81 40 41, g32p_row17_traceSegment_075_0081_0040, g32p_row17_traceSegment_075_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_075 0 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 0 81 81, g32p_row17_traceSegment_075_0000_0081, g32p_row17_traceSegment_075_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 162 10 10, g32p_row17_traceSegment_075_0162_0010, g32p_row17_traceSegment_075_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 182 10 10, g32p_row17_traceSegment_075_0182_0010, g32p_row17_traceSegment_075_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 162 20 20, g32p_row17_traceSegment_075_0162_0020, g32p_row17_traceSegment_075_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 202 10 10, g32p_row17_traceSegment_075_0202_0010, g32p_row17_traceSegment_075_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 222 10 11, g32p_row17_traceSegment_075_0222_0010, g32p_row17_traceSegment_075_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 202 20 21, g32p_row17_traceSegment_075_0202_0020, g32p_row17_traceSegment_075_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 162 40 41, g32p_row17_traceSegment_075_0162_0040, g32p_row17_traceSegment_075_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 243 10 10, g32p_row17_traceSegment_075_0243_0010, g32p_row17_traceSegment_075_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 263 10 10, g32p_row17_traceSegment_075_0263_0010, g32p_row17_traceSegment_075_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 243 20 20, g32p_row17_traceSegment_075_0243_0020, g32p_row17_traceSegment_075_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 283 10 10, g32p_row17_traceSegment_075_0283_0010, g32p_row17_traceSegment_075_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 303 10 11, g32p_row17_traceSegment_075_0303_0010, g32p_row17_traceSegment_075_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 283 20 21, g32p_row17_traceSegment_075_0283_0020, g32p_row17_traceSegment_075_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 243 40 41, g32p_row17_traceSegment_075_0243_0040, g32p_row17_traceSegment_075_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_075 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 162 81 81, g32p_row17_traceSegment_075_0162_0081, g32p_row17_traceSegment_075_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_075 0 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 0 162 162, g32p_row17_traceSegment_075_0000_0162, g32p_row17_traceSegment_075_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 324 10 10, g32p_row17_traceSegment_075_0324_0010, g32p_row17_traceSegment_075_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 344 10 10, g32p_row17_traceSegment_075_0344_0010, g32p_row17_traceSegment_075_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 324 20 20, g32p_row17_traceSegment_075_0324_0020, g32p_row17_traceSegment_075_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 364 10 10, g32p_row17_traceSegment_075_0364_0010, g32p_row17_traceSegment_075_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 394 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 384 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 384 10 11, g32p_row17_traceSegment_075_0384_0010, g32p_row17_traceSegment_075_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 364 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 364 20 21, g32p_row17_traceSegment_075_0364_0020, g32p_row17_traceSegment_075_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 324 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 324 40 41, g32p_row17_traceSegment_075_0324_0040, g32p_row17_traceSegment_075_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 405 10 10, g32p_row17_traceSegment_075_0405_0010, g32p_row17_traceSegment_075_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 425 10 10, g32p_row17_traceSegment_075_0425_0010, g32p_row17_traceSegment_075_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 405 20 20, g32p_row17_traceSegment_075_0405_0020, g32p_row17_traceSegment_075_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 445 10 10, g32p_row17_traceSegment_075_0445_0010, g32p_row17_traceSegment_075_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 475 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 465 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 465 10 11, g32p_row17_traceSegment_075_0465_0010, g32p_row17_traceSegment_075_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 445 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 445 20 21, g32p_row17_traceSegment_075_0445_0020, g32p_row17_traceSegment_075_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 405 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 405 40 41, g32p_row17_traceSegment_075_0405_0040, g32p_row17_traceSegment_075_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_075 324 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 324 81 81, g32p_row17_traceSegment_075_0324_0081, g32p_row17_traceSegment_075_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 486 10 10, g32p_row17_traceSegment_075_0486_0010, g32p_row17_traceSegment_075_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 506 10 10, g32p_row17_traceSegment_075_0506_0010, g32p_row17_traceSegment_075_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 486 20 20, g32p_row17_traceSegment_075_0486_0020, g32p_row17_traceSegment_075_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 526 10 10, g32p_row17_traceSegment_075_0526_0010, g32p_row17_traceSegment_075_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 546 10 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 546 21 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 546 10 11, g32p_row17_traceSegment_075_0546_0010, g32p_row17_traceSegment_075_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 526 41 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 526 20 21, g32p_row17_traceSegment_075_0526_0020, g32p_row17_traceSegment_075_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 486 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 486 40 41, g32p_row17_traceSegment_075_0486_0040, g32p_row17_traceSegment_075_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 567 10 10, g32p_row17_traceSegment_075_0567_0010, g32p_row17_traceSegment_075_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 587 10 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 587 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 587 10 10, g32p_row17_traceSegment_075_0587_0010, g32p_row17_traceSegment_075_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 567 40 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 567 20 20, g32p_row17_traceSegment_075_0567_0020, g32p_row17_traceSegment_075_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 617 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 607 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 607 10 10, g32p_row17_traceSegment_075_0607_0010, g32p_row17_traceSegment_075_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 627 10 11, g32p_row17_traceSegment_075_0627_0010, g32p_row17_traceSegment_075_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 607 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 607 20 21, g32p_row17_traceSegment_075_0607_0020, g32p_row17_traceSegment_075_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 567 81 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 567 40 41, g32p_row17_traceSegment_075_0567_0040, g32p_row17_traceSegment_075_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_075 486 162 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 486 81 81, g32p_row17_traceSegment_075_0486_0081, g32p_row17_traceSegment_075_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_075 324 324 = [7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 324 162 162, g32p_row17_traceSegment_075_0324_0162, g32p_row17_traceSegment_075_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_075 0 648 = [8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 0 324 324, g32p_row17_traceSegment_075_0000_0324, g32p_row17_traceSegment_075_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 648 10 10, g32p_row17_traceSegment_075_0648_0010, g32p_row17_traceSegment_075_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 668 10 10, g32p_row17_traceSegment_075_0668_0010, g32p_row17_traceSegment_075_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 648 20 20, g32p_row17_traceSegment_075_0648_0020, g32p_row17_traceSegment_075_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 688 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 688 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 688 10 10, g32p_row17_traceSegment_075_0688_0010, g32p_row17_traceSegment_075_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 708 10 11, g32p_row17_traceSegment_075_0708_0010, g32p_row17_traceSegment_075_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 688 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 688 20 21, g32p_row17_traceSegment_075_0688_0020, g32p_row17_traceSegment_075_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 648 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 648 40 41, g32p_row17_traceSegment_075_0648_0040, g32p_row17_traceSegment_075_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 729 10 10, g32p_row17_traceSegment_075_0729_0010, g32p_row17_traceSegment_075_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 749 10 10, g32p_row17_traceSegment_075_0749_0010, g32p_row17_traceSegment_075_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 729 20 20, g32p_row17_traceSegment_075_0729_0020, g32p_row17_traceSegment_075_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 769 10 10, g32p_row17_traceSegment_075_0769_0010, g32p_row17_traceSegment_075_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 789 10 11, g32p_row17_traceSegment_075_0789_0010, g32p_row17_traceSegment_075_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 769 20 21, g32p_row17_traceSegment_075_0769_0020, g32p_row17_traceSegment_075_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 729 40 41, g32p_row17_traceSegment_075_0729_0040, g32p_row17_traceSegment_075_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_075 648 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 648 81 81, g32p_row17_traceSegment_075_0648_0081, g32p_row17_traceSegment_075_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 810 10 10, g32p_row17_traceSegment_075_0810_0010, g32p_row17_traceSegment_075_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 830 10 10, g32p_row17_traceSegment_075_0830_0010, g32p_row17_traceSegment_075_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 810 20 20, g32p_row17_traceSegment_075_0810_0020, g32p_row17_traceSegment_075_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 850 10 10, g32p_row17_traceSegment_075_0850_0010, g32p_row17_traceSegment_075_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 870 10 11, g32p_row17_traceSegment_075_0870_0010, g32p_row17_traceSegment_075_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 850 20 21, g32p_row17_traceSegment_075_0850_0020, g32p_row17_traceSegment_075_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 810 40 41, g32p_row17_traceSegment_075_0810_0040, g32p_row17_traceSegment_075_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 891 10 10, g32p_row17_traceSegment_075_0891_0010, g32p_row17_traceSegment_075_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 911 10 10, g32p_row17_traceSegment_075_0911_0010, g32p_row17_traceSegment_075_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 891 20 20, g32p_row17_traceSegment_075_0891_0020, g32p_row17_traceSegment_075_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 931 10 10, g32p_row17_traceSegment_075_0931_0010, g32p_row17_traceSegment_075_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 951 10 11, g32p_row17_traceSegment_075_0951_0010, g32p_row17_traceSegment_075_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 931 20 21, g32p_row17_traceSegment_075_0931_0020, g32p_row17_traceSegment_075_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 891 40 41, g32p_row17_traceSegment_075_0891_0040, g32p_row17_traceSegment_075_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_075 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 810 81 81, g32p_row17_traceSegment_075_0810_0081, g32p_row17_traceSegment_075_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_075 648 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 648 162 162, g32p_row17_traceSegment_075_0648_0162, g32p_row17_traceSegment_075_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 972 10 10, g32p_row17_traceSegment_075_0972_0010, g32p_row17_traceSegment_075_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 992 10 10, g32p_row17_traceSegment_075_0992_0010, g32p_row17_traceSegment_075_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 972 20 20, g32p_row17_traceSegment_075_0972_0020, g32p_row17_traceSegment_075_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1012 10 10, g32p_row17_traceSegment_075_1012_0010, g32p_row17_traceSegment_075_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1032 10 11, g32p_row17_traceSegment_075_1032_0010, g32p_row17_traceSegment_075_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1012 20 21, g32p_row17_traceSegment_075_1012_0020, g32p_row17_traceSegment_075_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 972 40 41, g32p_row17_traceSegment_075_0972_0040, g32p_row17_traceSegment_075_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1053 10 10, g32p_row17_traceSegment_075_1053_0010, g32p_row17_traceSegment_075_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1073 10 10, g32p_row17_traceSegment_075_1073_0010, g32p_row17_traceSegment_075_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1053 20 20, g32p_row17_traceSegment_075_1053_0020, g32p_row17_traceSegment_075_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1093 10 10, g32p_row17_traceSegment_075_1093_0010, g32p_row17_traceSegment_075_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1113 10 11, g32p_row17_traceSegment_075_1113_0010, g32p_row17_traceSegment_075_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1093 20 21, g32p_row17_traceSegment_075_1093_0020, g32p_row17_traceSegment_075_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1053 40 41, g32p_row17_traceSegment_075_1053_0040, g32p_row17_traceSegment_075_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_075 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 972 81 81, g32p_row17_traceSegment_075_0972_0081, g32p_row17_traceSegment_075_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1134 10 10, g32p_row17_traceSegment_075_1134_0010, g32p_row17_traceSegment_075_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1154 10 10, g32p_row17_traceSegment_075_1154_0010, g32p_row17_traceSegment_075_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1134 20 20, g32p_row17_traceSegment_075_1134_0020, g32p_row17_traceSegment_075_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1174 10 10, g32p_row17_traceSegment_075_1174_0010, g32p_row17_traceSegment_075_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1194 10 11, g32p_row17_traceSegment_075_1194_0010, g32p_row17_traceSegment_075_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1174 20 21, g32p_row17_traceSegment_075_1174_0020, g32p_row17_traceSegment_075_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1134 40 41, g32p_row17_traceSegment_075_1134_0040, g32p_row17_traceSegment_075_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1215 10 10, g32p_row17_traceSegment_075_1215_0010, g32p_row17_traceSegment_075_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1235 10 10, g32p_row17_traceSegment_075_1235_0010, g32p_row17_traceSegment_075_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_075 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1215 20 20, g32p_row17_traceSegment_075_1215_0020, g32p_row17_traceSegment_075_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1265 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_075 1255 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1255 10 10, g32p_row17_traceSegment_075_1255_0010, g32p_row17_traceSegment_075_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_075 1275 10 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_075 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_075_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_075 1275 21 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1275 10 11, g32p_row17_traceSegment_075_1275_0010, g32p_row17_traceSegment_075_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_075 1255 41 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1255 20 21, g32p_row17_traceSegment_075_1255_0020, g32p_row17_traceSegment_075_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_075 1215 81 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1215 40 41, g32p_row17_traceSegment_075_1215_0040, g32p_row17_traceSegment_075_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_075_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_075 1134 162 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 1134 81 81, g32p_row17_traceSegment_075_1134_0081, g32p_row17_traceSegment_075_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_075 972 324 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 972 162 162, g32p_row17_traceSegment_075_0972_0162, g32p_row17_traceSegment_075_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_075 648 648 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 648 324 324, g32p_row17_traceSegment_075_0648_0324, g32p_row17_traceSegment_075_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_075_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_075 0 1296 = [12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_075 0 648 648, g32p_row17_traceSegment_075_0000_0648, g32p_row17_traceSegment_075_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 75 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_075_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_076 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 76 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_076_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 0 10 10, g32p_row17_traceSegment_076_0000_0010, g32p_row17_traceSegment_076_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 20 10 10, g32p_row17_traceSegment_076_0020_0010, g32p_row17_traceSegment_076_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 0 20 20, g32p_row17_traceSegment_076_0000_0020, g32p_row17_traceSegment_076_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 40 10 10, g32p_row17_traceSegment_076_0040_0010, g32p_row17_traceSegment_076_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 60 10 11, g32p_row17_traceSegment_076_0060_0010, g32p_row17_traceSegment_076_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 40 20 21, g32p_row17_traceSegment_076_0040_0020, g32p_row17_traceSegment_076_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 0 40 41, g32p_row17_traceSegment_076_0000_0040, g32p_row17_traceSegment_076_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 81 10 10, g32p_row17_traceSegment_076_0081_0010, g32p_row17_traceSegment_076_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 101 10 10, g32p_row17_traceSegment_076_0101_0010, g32p_row17_traceSegment_076_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 81 20 20, g32p_row17_traceSegment_076_0081_0020, g32p_row17_traceSegment_076_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 121 10 10, g32p_row17_traceSegment_076_0121_0010, g32p_row17_traceSegment_076_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 141 10 11, g32p_row17_traceSegment_076_0141_0010, g32p_row17_traceSegment_076_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 121 20 21, g32p_row17_traceSegment_076_0121_0020, g32p_row17_traceSegment_076_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 81 40 41, g32p_row17_traceSegment_076_0081_0040, g32p_row17_traceSegment_076_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_076 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 0 81 81, g32p_row17_traceSegment_076_0000_0081, g32p_row17_traceSegment_076_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 162 10 10, g32p_row17_traceSegment_076_0162_0010, g32p_row17_traceSegment_076_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 182 10 10, g32p_row17_traceSegment_076_0182_0010, g32p_row17_traceSegment_076_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 162 20 20, g32p_row17_traceSegment_076_0162_0020, g32p_row17_traceSegment_076_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 202 10 10, g32p_row17_traceSegment_076_0202_0010, g32p_row17_traceSegment_076_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 222 10 11, g32p_row17_traceSegment_076_0222_0010, g32p_row17_traceSegment_076_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 202 20 21, g32p_row17_traceSegment_076_0202_0020, g32p_row17_traceSegment_076_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 162 40 41, g32p_row17_traceSegment_076_0162_0040, g32p_row17_traceSegment_076_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 243 10 10, g32p_row17_traceSegment_076_0243_0010, g32p_row17_traceSegment_076_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 263 10 10, g32p_row17_traceSegment_076_0263_0010, g32p_row17_traceSegment_076_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 243 20 20, g32p_row17_traceSegment_076_0243_0020, g32p_row17_traceSegment_076_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 283 10 10, g32p_row17_traceSegment_076_0283_0010, g32p_row17_traceSegment_076_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 303 10 11, g32p_row17_traceSegment_076_0303_0010, g32p_row17_traceSegment_076_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 283 20 21, g32p_row17_traceSegment_076_0283_0020, g32p_row17_traceSegment_076_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 243 40 41, g32p_row17_traceSegment_076_0243_0040, g32p_row17_traceSegment_076_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_076 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 162 81 81, g32p_row17_traceSegment_076_0162_0081, g32p_row17_traceSegment_076_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_076 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 0 162 162, g32p_row17_traceSegment_076_0000_0162, g32p_row17_traceSegment_076_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 324 10 10, g32p_row17_traceSegment_076_0324_0010, g32p_row17_traceSegment_076_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 344 10 10, g32p_row17_traceSegment_076_0344_0010, g32p_row17_traceSegment_076_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 324 20 20, g32p_row17_traceSegment_076_0324_0020, g32p_row17_traceSegment_076_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 364 10 10, g32p_row17_traceSegment_076_0364_0010, g32p_row17_traceSegment_076_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 384 10 11, g32p_row17_traceSegment_076_0384_0010, g32p_row17_traceSegment_076_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 364 20 21, g32p_row17_traceSegment_076_0364_0020, g32p_row17_traceSegment_076_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 324 40 41, g32p_row17_traceSegment_076_0324_0040, g32p_row17_traceSegment_076_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 405 10 10, g32p_row17_traceSegment_076_0405_0010, g32p_row17_traceSegment_076_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 425 10 10, g32p_row17_traceSegment_076_0425_0010, g32p_row17_traceSegment_076_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 405 20 20, g32p_row17_traceSegment_076_0405_0020, g32p_row17_traceSegment_076_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 445 10 10, g32p_row17_traceSegment_076_0445_0010, g32p_row17_traceSegment_076_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 465 10 11, g32p_row17_traceSegment_076_0465_0010, g32p_row17_traceSegment_076_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 445 20 21, g32p_row17_traceSegment_076_0445_0020, g32p_row17_traceSegment_076_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 405 40 41, g32p_row17_traceSegment_076_0405_0040, g32p_row17_traceSegment_076_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_076 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 324 81 81, g32p_row17_traceSegment_076_0324_0081, g32p_row17_traceSegment_076_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 486 10 10, g32p_row17_traceSegment_076_0486_0010, g32p_row17_traceSegment_076_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 506 10 10, g32p_row17_traceSegment_076_0506_0010, g32p_row17_traceSegment_076_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 486 20 20, g32p_row17_traceSegment_076_0486_0020, g32p_row17_traceSegment_076_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 526 10 10, g32p_row17_traceSegment_076_0526_0010, g32p_row17_traceSegment_076_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 546 10 11, g32p_row17_traceSegment_076_0546_0010, g32p_row17_traceSegment_076_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 526 20 21, g32p_row17_traceSegment_076_0526_0020, g32p_row17_traceSegment_076_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 486 40 41, g32p_row17_traceSegment_076_0486_0040, g32p_row17_traceSegment_076_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 567 10 10, g32p_row17_traceSegment_076_0567_0010, g32p_row17_traceSegment_076_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 587 10 10, g32p_row17_traceSegment_076_0587_0010, g32p_row17_traceSegment_076_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 567 20 20, g32p_row17_traceSegment_076_0567_0020, g32p_row17_traceSegment_076_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 607 10 10, g32p_row17_traceSegment_076_0607_0010, g32p_row17_traceSegment_076_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 627 10 11, g32p_row17_traceSegment_076_0627_0010, g32p_row17_traceSegment_076_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 607 20 21, g32p_row17_traceSegment_076_0607_0020, g32p_row17_traceSegment_076_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 567 40 41, g32p_row17_traceSegment_076_0567_0040, g32p_row17_traceSegment_076_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_076 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 486 81 81, g32p_row17_traceSegment_076_0486_0081, g32p_row17_traceSegment_076_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_076 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 324 162 162, g32p_row17_traceSegment_076_0324_0162, g32p_row17_traceSegment_076_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_076 0 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 0 324 324, g32p_row17_traceSegment_076_0000_0324, g32p_row17_traceSegment_076_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 648 10 10, g32p_row17_traceSegment_076_0648_0010, g32p_row17_traceSegment_076_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 668 10 10, g32p_row17_traceSegment_076_0668_0010, g32p_row17_traceSegment_076_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 648 20 20, g32p_row17_traceSegment_076_0648_0020, g32p_row17_traceSegment_076_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 688 10 10, g32p_row17_traceSegment_076_0688_0010, g32p_row17_traceSegment_076_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 708 10 11, g32p_row17_traceSegment_076_0708_0010, g32p_row17_traceSegment_076_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 688 20 21, g32p_row17_traceSegment_076_0688_0020, g32p_row17_traceSegment_076_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 648 40 41, g32p_row17_traceSegment_076_0648_0040, g32p_row17_traceSegment_076_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 729 10 10, g32p_row17_traceSegment_076_0729_0010, g32p_row17_traceSegment_076_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 749 10 10, g32p_row17_traceSegment_076_0749_0010, g32p_row17_traceSegment_076_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 729 20 20, g32p_row17_traceSegment_076_0729_0020, g32p_row17_traceSegment_076_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 769 10 10, g32p_row17_traceSegment_076_0769_0010, g32p_row17_traceSegment_076_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 789 10 11, g32p_row17_traceSegment_076_0789_0010, g32p_row17_traceSegment_076_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 769 20 21, g32p_row17_traceSegment_076_0769_0020, g32p_row17_traceSegment_076_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 729 40 41, g32p_row17_traceSegment_076_0729_0040, g32p_row17_traceSegment_076_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_076 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 648 81 81, g32p_row17_traceSegment_076_0648_0081, g32p_row17_traceSegment_076_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 810 10 10, g32p_row17_traceSegment_076_0810_0010, g32p_row17_traceSegment_076_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 830 10 10, g32p_row17_traceSegment_076_0830_0010, g32p_row17_traceSegment_076_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 810 20 20, g32p_row17_traceSegment_076_0810_0020, g32p_row17_traceSegment_076_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 850 10 10, g32p_row17_traceSegment_076_0850_0010, g32p_row17_traceSegment_076_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 870 10 11, g32p_row17_traceSegment_076_0870_0010, g32p_row17_traceSegment_076_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 850 20 21, g32p_row17_traceSegment_076_0850_0020, g32p_row17_traceSegment_076_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 810 40 41, g32p_row17_traceSegment_076_0810_0040, g32p_row17_traceSegment_076_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 891 10 10, g32p_row17_traceSegment_076_0891_0010, g32p_row17_traceSegment_076_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 911 10 10, g32p_row17_traceSegment_076_0911_0010, g32p_row17_traceSegment_076_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 891 20 20, g32p_row17_traceSegment_076_0891_0020, g32p_row17_traceSegment_076_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 931 10 10, g32p_row17_traceSegment_076_0931_0010, g32p_row17_traceSegment_076_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 951 10 11, g32p_row17_traceSegment_076_0951_0010, g32p_row17_traceSegment_076_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 931 20 21, g32p_row17_traceSegment_076_0931_0020, g32p_row17_traceSegment_076_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 891 40 41, g32p_row17_traceSegment_076_0891_0040, g32p_row17_traceSegment_076_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_076 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 810 81 81, g32p_row17_traceSegment_076_0810_0081, g32p_row17_traceSegment_076_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_076 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 648 162 162, g32p_row17_traceSegment_076_0648_0162, g32p_row17_traceSegment_076_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 972 10 10, g32p_row17_traceSegment_076_0972_0010, g32p_row17_traceSegment_076_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 992 10 10, g32p_row17_traceSegment_076_0992_0010, g32p_row17_traceSegment_076_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 972 20 20, g32p_row17_traceSegment_076_0972_0020, g32p_row17_traceSegment_076_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1012 10 10, g32p_row17_traceSegment_076_1012_0010, g32p_row17_traceSegment_076_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1032 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 1032 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1032 10 11, g32p_row17_traceSegment_076_1032_0010, g32p_row17_traceSegment_076_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 1012 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1012 20 21, g32p_row17_traceSegment_076_1012_0020, g32p_row17_traceSegment_076_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 972 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 972 40 41, g32p_row17_traceSegment_076_0972_0040, g32p_row17_traceSegment_076_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1053 10 10, g32p_row17_traceSegment_076_1053_0010, g32p_row17_traceSegment_076_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1073 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 1073 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1073 10 10, g32p_row17_traceSegment_076_1073_0010, g32p_row17_traceSegment_076_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 1053 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1053 20 20, g32p_row17_traceSegment_076_1053_0020, g32p_row17_traceSegment_076_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1103 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 1093 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1093 10 10, g32p_row17_traceSegment_076_1093_0010, g32p_row17_traceSegment_076_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 1123 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 1113 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1113 10 11, g32p_row17_traceSegment_076_1113_0010, g32p_row17_traceSegment_076_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 1093 41 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1093 20 21, g32p_row17_traceSegment_076_1093_0020, g32p_row17_traceSegment_076_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 1053 81 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1053 40 41, g32p_row17_traceSegment_076_1053_0040, g32p_row17_traceSegment_076_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_076 972 162 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 972 81 81, g32p_row17_traceSegment_076_0972_0081, g32p_row17_traceSegment_076_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1134 10 10, g32p_row17_traceSegment_076_1134_0010, g32p_row17_traceSegment_076_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1154 10 10, g32p_row17_traceSegment_076_1154_0010, g32p_row17_traceSegment_076_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1134 20 20, g32p_row17_traceSegment_076_1134_0020, g32p_row17_traceSegment_076_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1174 10 10, g32p_row17_traceSegment_076_1174_0010, g32p_row17_traceSegment_076_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1194 10 11, g32p_row17_traceSegment_076_1194_0010, g32p_row17_traceSegment_076_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1174 20 21, g32p_row17_traceSegment_076_1174_0020, g32p_row17_traceSegment_076_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1134 40 41, g32p_row17_traceSegment_076_1134_0040, g32p_row17_traceSegment_076_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1215 10 10, g32p_row17_traceSegment_076_1215_0010, g32p_row17_traceSegment_076_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1235 10 10, g32p_row17_traceSegment_076_1235_0010, g32p_row17_traceSegment_076_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_076 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1215 20 20, g32p_row17_traceSegment_076_1215_0020, g32p_row17_traceSegment_076_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_076 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1255 10 10, g32p_row17_traceSegment_076_1255_0010, g32p_row17_traceSegment_076_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_076 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_076 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_076_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_076 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1275 10 11, g32p_row17_traceSegment_076_1275_0010, g32p_row17_traceSegment_076_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_076 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1255 20 21, g32p_row17_traceSegment_076_1255_0020, g32p_row17_traceSegment_076_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_076 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1215 40 41, g32p_row17_traceSegment_076_1215_0040, g32p_row17_traceSegment_076_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_076_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_076 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 1134 81 81, g32p_row17_traceSegment_076_1134_0081, g32p_row17_traceSegment_076_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_076 972 324 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 972 162 162, g32p_row17_traceSegment_076_0972_0162, g32p_row17_traceSegment_076_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_076 648 648 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 648 324 324, g32p_row17_traceSegment_076_0648_0324, g32p_row17_traceSegment_076_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_076_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_076 0 1296 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_076 0 648 648, g32p_row17_traceSegment_076_0000_0648, g32p_row17_traceSegment_076_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 76 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_076_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_077 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 77 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_077_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 0 10 10, g32p_row17_traceSegment_077_0000_0010, g32p_row17_traceSegment_077_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 20 10 10, g32p_row17_traceSegment_077_0020_0010, g32p_row17_traceSegment_077_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 0 20 20, g32p_row17_traceSegment_077_0000_0020, g32p_row17_traceSegment_077_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 40 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 50 10 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 40 20 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 40 10 10, g32p_row17_traceSegment_077_0040_0010, g32p_row17_traceSegment_077_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 60 10 11, g32p_row17_traceSegment_077_0060_0010, g32p_row17_traceSegment_077_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 40 41 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 40 20 21, g32p_row17_traceSegment_077_0040_0020, g32p_row17_traceSegment_077_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 0 81 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 0 40 41, g32p_row17_traceSegment_077_0000_0040, g32p_row17_traceSegment_077_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 81 10 10, g32p_row17_traceSegment_077_0081_0010, g32p_row17_traceSegment_077_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 101 10 10, g32p_row17_traceSegment_077_0101_0010, g32p_row17_traceSegment_077_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 81 20 20, g32p_row17_traceSegment_077_0081_0020, g32p_row17_traceSegment_077_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 121 10 10, g32p_row17_traceSegment_077_0121_0010, g32p_row17_traceSegment_077_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 141 10 11, g32p_row17_traceSegment_077_0141_0010, g32p_row17_traceSegment_077_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 121 20 21, g32p_row17_traceSegment_077_0121_0020, g32p_row17_traceSegment_077_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 81 40 41, g32p_row17_traceSegment_077_0081_0040, g32p_row17_traceSegment_077_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_077 0 162 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 0 81 81, g32p_row17_traceSegment_077_0000_0081, g32p_row17_traceSegment_077_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 162 10 10, g32p_row17_traceSegment_077_0162_0010, g32p_row17_traceSegment_077_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 182 10 10, g32p_row17_traceSegment_077_0182_0010, g32p_row17_traceSegment_077_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 162 20 20, g32p_row17_traceSegment_077_0162_0020, g32p_row17_traceSegment_077_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 202 10 10, g32p_row17_traceSegment_077_0202_0010, g32p_row17_traceSegment_077_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 222 10 11, g32p_row17_traceSegment_077_0222_0010, g32p_row17_traceSegment_077_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 202 20 21, g32p_row17_traceSegment_077_0202_0020, g32p_row17_traceSegment_077_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 162 40 41, g32p_row17_traceSegment_077_0162_0040, g32p_row17_traceSegment_077_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 243 10 10, g32p_row17_traceSegment_077_0243_0010, g32p_row17_traceSegment_077_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 273 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 263 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 263 10 10, g32p_row17_traceSegment_077_0263_0010, g32p_row17_traceSegment_077_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 243 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 243 20 20, g32p_row17_traceSegment_077_0243_0020, g32p_row17_traceSegment_077_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 283 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 283 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 283 10 10, g32p_row17_traceSegment_077_0283_0010, g32p_row17_traceSegment_077_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 303 10 11, g32p_row17_traceSegment_077_0303_0010, g32p_row17_traceSegment_077_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 283 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 283 20 21, g32p_row17_traceSegment_077_0283_0020, g32p_row17_traceSegment_077_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 243 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 243 40 41, g32p_row17_traceSegment_077_0243_0040, g32p_row17_traceSegment_077_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_077 162 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 162 81 81, g32p_row17_traceSegment_077_0162_0081, g32p_row17_traceSegment_077_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_077 0 324 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 0 162 162, g32p_row17_traceSegment_077_0000_0162, g32p_row17_traceSegment_077_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 324 10 10, g32p_row17_traceSegment_077_0324_0010, g32p_row17_traceSegment_077_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 344 10 10, g32p_row17_traceSegment_077_0344_0010, g32p_row17_traceSegment_077_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 324 20 20, g32p_row17_traceSegment_077_0324_0020, g32p_row17_traceSegment_077_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 364 10 10, g32p_row17_traceSegment_077_0364_0010, g32p_row17_traceSegment_077_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 394 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 384 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 384 10 11, g32p_row17_traceSegment_077_0384_0010, g32p_row17_traceSegment_077_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 364 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 364 20 21, g32p_row17_traceSegment_077_0364_0020, g32p_row17_traceSegment_077_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 324 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 324 40 41, g32p_row17_traceSegment_077_0324_0040, g32p_row17_traceSegment_077_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 405 10 10, g32p_row17_traceSegment_077_0405_0010, g32p_row17_traceSegment_077_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 425 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 425 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 425 10 10, g32p_row17_traceSegment_077_0425_0010, g32p_row17_traceSegment_077_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 405 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 405 20 20, g32p_row17_traceSegment_077_0405_0020, g32p_row17_traceSegment_077_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 445 10 10, g32p_row17_traceSegment_077_0445_0010, g32p_row17_traceSegment_077_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 465 10 11, g32p_row17_traceSegment_077_0465_0010, g32p_row17_traceSegment_077_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 445 20 21, g32p_row17_traceSegment_077_0445_0020, g32p_row17_traceSegment_077_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 405 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 405 40 41, g32p_row17_traceSegment_077_0405_0040, g32p_row17_traceSegment_077_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_077 324 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 324 81 81, g32p_row17_traceSegment_077_0324_0081, g32p_row17_traceSegment_077_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 486 10 10, g32p_row17_traceSegment_077_0486_0010, g32p_row17_traceSegment_077_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 506 10 10, g32p_row17_traceSegment_077_0506_0010, g32p_row17_traceSegment_077_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 486 20 20, g32p_row17_traceSegment_077_0486_0020, g32p_row17_traceSegment_077_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 526 10 10, g32p_row17_traceSegment_077_0526_0010, g32p_row17_traceSegment_077_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 546 10 11, g32p_row17_traceSegment_077_0546_0010, g32p_row17_traceSegment_077_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 526 20 21, g32p_row17_traceSegment_077_0526_0020, g32p_row17_traceSegment_077_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 486 40 41, g32p_row17_traceSegment_077_0486_0040, g32p_row17_traceSegment_077_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 567 10 10, g32p_row17_traceSegment_077_0567_0010, g32p_row17_traceSegment_077_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 587 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 587 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 587 10 10, g32p_row17_traceSegment_077_0587_0010, g32p_row17_traceSegment_077_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 567 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 567 20 20, g32p_row17_traceSegment_077_0567_0020, g32p_row17_traceSegment_077_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 607 10 10, g32p_row17_traceSegment_077_0607_0010, g32p_row17_traceSegment_077_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 627 10 11, g32p_row17_traceSegment_077_0627_0010, g32p_row17_traceSegment_077_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 607 20 21, g32p_row17_traceSegment_077_0607_0020, g32p_row17_traceSegment_077_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 567 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 567 40 41, g32p_row17_traceSegment_077_0567_0040, g32p_row17_traceSegment_077_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_077 486 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 486 81 81, g32p_row17_traceSegment_077_0486_0081, g32p_row17_traceSegment_077_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_077 324 324 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 324 162 162, g32p_row17_traceSegment_077_0324_0162, g32p_row17_traceSegment_077_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_077 0 648 = [8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 0 324 324, g32p_row17_traceSegment_077_0000_0324, g32p_row17_traceSegment_077_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 648 10 10, g32p_row17_traceSegment_077_0648_0010, g32p_row17_traceSegment_077_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 668 10 10, g32p_row17_traceSegment_077_0668_0010, g32p_row17_traceSegment_077_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 648 20 20, g32p_row17_traceSegment_077_0648_0020, g32p_row17_traceSegment_077_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 688 10 10, g32p_row17_traceSegment_077_0688_0010, g32p_row17_traceSegment_077_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 708 10 11, g32p_row17_traceSegment_077_0708_0010, g32p_row17_traceSegment_077_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 688 20 21, g32p_row17_traceSegment_077_0688_0020, g32p_row17_traceSegment_077_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 648 40 41, g32p_row17_traceSegment_077_0648_0040, g32p_row17_traceSegment_077_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 729 10 10, g32p_row17_traceSegment_077_0729_0010, g32p_row17_traceSegment_077_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 749 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 749 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 749 10 10, g32p_row17_traceSegment_077_0749_0010, g32p_row17_traceSegment_077_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 729 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 729 20 20, g32p_row17_traceSegment_077_0729_0020, g32p_row17_traceSegment_077_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 769 10 10, g32p_row17_traceSegment_077_0769_0010, g32p_row17_traceSegment_077_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 789 10 11, g32p_row17_traceSegment_077_0789_0010, g32p_row17_traceSegment_077_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 769 20 21, g32p_row17_traceSegment_077_0769_0020, g32p_row17_traceSegment_077_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 729 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 729 40 41, g32p_row17_traceSegment_077_0729_0040, g32p_row17_traceSegment_077_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_077 648 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 648 81 81, g32p_row17_traceSegment_077_0648_0081, g32p_row17_traceSegment_077_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 820 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 810 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 810 10 10, g32p_row17_traceSegment_077_0810_0010, g32p_row17_traceSegment_077_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 830 10 10, g32p_row17_traceSegment_077_0830_0010, g32p_row17_traceSegment_077_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 810 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 810 20 20, g32p_row17_traceSegment_077_0810_0020, g32p_row17_traceSegment_077_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 850 10 10, g32p_row17_traceSegment_077_0850_0010, g32p_row17_traceSegment_077_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 870 10 11, g32p_row17_traceSegment_077_0870_0010, g32p_row17_traceSegment_077_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 850 20 21, g32p_row17_traceSegment_077_0850_0020, g32p_row17_traceSegment_077_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 810 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 810 40 41, g32p_row17_traceSegment_077_0810_0040, g32p_row17_traceSegment_077_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 891 10 10, g32p_row17_traceSegment_077_0891_0010, g32p_row17_traceSegment_077_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 911 10 10, g32p_row17_traceSegment_077_0911_0010, g32p_row17_traceSegment_077_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 891 20 20, g32p_row17_traceSegment_077_0891_0020, g32p_row17_traceSegment_077_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 931 10 10, g32p_row17_traceSegment_077_0931_0010, g32p_row17_traceSegment_077_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 961 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 951 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 951 10 11, g32p_row17_traceSegment_077_0951_0010, g32p_row17_traceSegment_077_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 931 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 931 20 21, g32p_row17_traceSegment_077_0931_0020, g32p_row17_traceSegment_077_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 891 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 891 40 41, g32p_row17_traceSegment_077_0891_0040, g32p_row17_traceSegment_077_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_077 810 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 810 81 81, g32p_row17_traceSegment_077_0810_0081, g32p_row17_traceSegment_077_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_077 648 324 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 648 162 162, g32p_row17_traceSegment_077_0648_0162, g32p_row17_traceSegment_077_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 972 10 10, g32p_row17_traceSegment_077_0972_0010, g32p_row17_traceSegment_077_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 992 10 10, g32p_row17_traceSegment_077_0992_0010, g32p_row17_traceSegment_077_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 972 20 20, g32p_row17_traceSegment_077_0972_0020, g32p_row17_traceSegment_077_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1012 10 10, g32p_row17_traceSegment_077_1012_0010, g32p_row17_traceSegment_077_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1032 10 11, g32p_row17_traceSegment_077_1032_0010, g32p_row17_traceSegment_077_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1012 20 21, g32p_row17_traceSegment_077_1012_0020, g32p_row17_traceSegment_077_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 972 40 41, g32p_row17_traceSegment_077_0972_0040, g32p_row17_traceSegment_077_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1063 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 1053 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1053 10 10, g32p_row17_traceSegment_077_1053_0010, g32p_row17_traceSegment_077_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1073 10 10, g32p_row17_traceSegment_077_1073_0010, g32p_row17_traceSegment_077_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 1053 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1053 20 20, g32p_row17_traceSegment_077_1053_0020, g32p_row17_traceSegment_077_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1093 10 10, g32p_row17_traceSegment_077_1093_0010, g32p_row17_traceSegment_077_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1113 10 11, g32p_row17_traceSegment_077_1113_0010, g32p_row17_traceSegment_077_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1093 20 21, g32p_row17_traceSegment_077_1093_0020, g32p_row17_traceSegment_077_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 1053 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1053 40 41, g32p_row17_traceSegment_077_1053_0040, g32p_row17_traceSegment_077_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_077 972 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 972 81 81, g32p_row17_traceSegment_077_0972_0081, g32p_row17_traceSegment_077_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1134 10 10, g32p_row17_traceSegment_077_1134_0010, g32p_row17_traceSegment_077_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1154 10 10, g32p_row17_traceSegment_077_1154_0010, g32p_row17_traceSegment_077_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1134 20 20, g32p_row17_traceSegment_077_1134_0020, g32p_row17_traceSegment_077_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1174 10 10, g32p_row17_traceSegment_077_1174_0010, g32p_row17_traceSegment_077_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1194 10 11, g32p_row17_traceSegment_077_1194_0010, g32p_row17_traceSegment_077_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1174 20 21, g32p_row17_traceSegment_077_1174_0020, g32p_row17_traceSegment_077_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1134 40 41, g32p_row17_traceSegment_077_1134_0040, g32p_row17_traceSegment_077_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1215 10 10, g32p_row17_traceSegment_077_1215_0010, g32p_row17_traceSegment_077_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1235 10 10, g32p_row17_traceSegment_077_1235_0010, g32p_row17_traceSegment_077_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_077 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1215 20 20, g32p_row17_traceSegment_077_1215_0020, g32p_row17_traceSegment_077_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_077 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1255 10 10, g32p_row17_traceSegment_077_1255_0010, g32p_row17_traceSegment_077_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_077 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_077 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_077_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_077 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1275 10 11, g32p_row17_traceSegment_077_1275_0010, g32p_row17_traceSegment_077_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_077 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1255 20 21, g32p_row17_traceSegment_077_1255_0020, g32p_row17_traceSegment_077_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_077 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1215 40 41, g32p_row17_traceSegment_077_1215_0040, g32p_row17_traceSegment_077_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_077_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_077 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 1134 81 81, g32p_row17_traceSegment_077_1134_0081, g32p_row17_traceSegment_077_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_077 972 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 972 162 162, g32p_row17_traceSegment_077_0972_0162, g32p_row17_traceSegment_077_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_077 648 648 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 648 324 324, g32p_row17_traceSegment_077_0648_0324, g32p_row17_traceSegment_077_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_077_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_077 0 1296 = [12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_077 0 648 648, g32p_row17_traceSegment_077_0000_0648, g32p_row17_traceSegment_077_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 77 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_077_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_078 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 78 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_078_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 0 10 10, g32p_row17_traceSegment_078_0000_0010, g32p_row17_traceSegment_078_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 20 10 10, g32p_row17_traceSegment_078_0020_0010, g32p_row17_traceSegment_078_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 0 20 20, g32p_row17_traceSegment_078_0000_0020, g32p_row17_traceSegment_078_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 40 10 10, g32p_row17_traceSegment_078_0040_0010, g32p_row17_traceSegment_078_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 60 10 11, g32p_row17_traceSegment_078_0060_0010, g32p_row17_traceSegment_078_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 40 20 21, g32p_row17_traceSegment_078_0040_0020, g32p_row17_traceSegment_078_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 0 40 41, g32p_row17_traceSegment_078_0000_0040, g32p_row17_traceSegment_078_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 81 10 10, g32p_row17_traceSegment_078_0081_0010, g32p_row17_traceSegment_078_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 101 10 10, g32p_row17_traceSegment_078_0101_0010, g32p_row17_traceSegment_078_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 81 20 20, g32p_row17_traceSegment_078_0081_0020, g32p_row17_traceSegment_078_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 121 10 10, g32p_row17_traceSegment_078_0121_0010, g32p_row17_traceSegment_078_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 141 10 11, g32p_row17_traceSegment_078_0141_0010, g32p_row17_traceSegment_078_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 121 20 21, g32p_row17_traceSegment_078_0121_0020, g32p_row17_traceSegment_078_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 81 40 41, g32p_row17_traceSegment_078_0081_0040, g32p_row17_traceSegment_078_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_078 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 0 81 81, g32p_row17_traceSegment_078_0000_0081, g32p_row17_traceSegment_078_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 162 10 10, g32p_row17_traceSegment_078_0162_0010, g32p_row17_traceSegment_078_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 182 10 10, g32p_row17_traceSegment_078_0182_0010, g32p_row17_traceSegment_078_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 162 20 20, g32p_row17_traceSegment_078_0162_0020, g32p_row17_traceSegment_078_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 202 10 10, g32p_row17_traceSegment_078_0202_0010, g32p_row17_traceSegment_078_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 222 10 11, g32p_row17_traceSegment_078_0222_0010, g32p_row17_traceSegment_078_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 202 20 21, g32p_row17_traceSegment_078_0202_0020, g32p_row17_traceSegment_078_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 162 40 41, g32p_row17_traceSegment_078_0162_0040, g32p_row17_traceSegment_078_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 243 10 10, g32p_row17_traceSegment_078_0243_0010, g32p_row17_traceSegment_078_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 263 10 10, g32p_row17_traceSegment_078_0263_0010, g32p_row17_traceSegment_078_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 243 20 20, g32p_row17_traceSegment_078_0243_0020, g32p_row17_traceSegment_078_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 283 10 10, g32p_row17_traceSegment_078_0283_0010, g32p_row17_traceSegment_078_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 303 10 11, g32p_row17_traceSegment_078_0303_0010, g32p_row17_traceSegment_078_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 283 20 21, g32p_row17_traceSegment_078_0283_0020, g32p_row17_traceSegment_078_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 243 40 41, g32p_row17_traceSegment_078_0243_0040, g32p_row17_traceSegment_078_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_078 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 162 81 81, g32p_row17_traceSegment_078_0162_0081, g32p_row17_traceSegment_078_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_078 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 0 162 162, g32p_row17_traceSegment_078_0000_0162, g32p_row17_traceSegment_078_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 324 10 10, g32p_row17_traceSegment_078_0324_0010, g32p_row17_traceSegment_078_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 344 10 10, g32p_row17_traceSegment_078_0344_0010, g32p_row17_traceSegment_078_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 324 20 20, g32p_row17_traceSegment_078_0324_0020, g32p_row17_traceSegment_078_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 364 10 10, g32p_row17_traceSegment_078_0364_0010, g32p_row17_traceSegment_078_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 384 10 11, g32p_row17_traceSegment_078_0384_0010, g32p_row17_traceSegment_078_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 364 20 21, g32p_row17_traceSegment_078_0364_0020, g32p_row17_traceSegment_078_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 324 40 41, g32p_row17_traceSegment_078_0324_0040, g32p_row17_traceSegment_078_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 405 10 10, g32p_row17_traceSegment_078_0405_0010, g32p_row17_traceSegment_078_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 425 10 10, g32p_row17_traceSegment_078_0425_0010, g32p_row17_traceSegment_078_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 405 20 20, g32p_row17_traceSegment_078_0405_0020, g32p_row17_traceSegment_078_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 445 10 10, g32p_row17_traceSegment_078_0445_0010, g32p_row17_traceSegment_078_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 465 10 11, g32p_row17_traceSegment_078_0465_0010, g32p_row17_traceSegment_078_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 445 20 21, g32p_row17_traceSegment_078_0445_0020, g32p_row17_traceSegment_078_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 405 40 41, g32p_row17_traceSegment_078_0405_0040, g32p_row17_traceSegment_078_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_078 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 324 81 81, g32p_row17_traceSegment_078_0324_0081, g32p_row17_traceSegment_078_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 486 10 10, g32p_row17_traceSegment_078_0486_0010, g32p_row17_traceSegment_078_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 506 10 10, g32p_row17_traceSegment_078_0506_0010, g32p_row17_traceSegment_078_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 486 20 20, g32p_row17_traceSegment_078_0486_0020, g32p_row17_traceSegment_078_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 526 10 10, g32p_row17_traceSegment_078_0526_0010, g32p_row17_traceSegment_078_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 546 10 11, g32p_row17_traceSegment_078_0546_0010, g32p_row17_traceSegment_078_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 526 20 21, g32p_row17_traceSegment_078_0526_0020, g32p_row17_traceSegment_078_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 486 40 41, g32p_row17_traceSegment_078_0486_0040, g32p_row17_traceSegment_078_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 567 10 10, g32p_row17_traceSegment_078_0567_0010, g32p_row17_traceSegment_078_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 587 10 10, g32p_row17_traceSegment_078_0587_0010, g32p_row17_traceSegment_078_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 567 20 20, g32p_row17_traceSegment_078_0567_0020, g32p_row17_traceSegment_078_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 607 10 10, g32p_row17_traceSegment_078_0607_0010, g32p_row17_traceSegment_078_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 627 10 11, g32p_row17_traceSegment_078_0627_0010, g32p_row17_traceSegment_078_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 607 20 21, g32p_row17_traceSegment_078_0607_0020, g32p_row17_traceSegment_078_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 567 40 41, g32p_row17_traceSegment_078_0567_0040, g32p_row17_traceSegment_078_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_078 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 486 81 81, g32p_row17_traceSegment_078_0486_0081, g32p_row17_traceSegment_078_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_078 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 324 162 162, g32p_row17_traceSegment_078_0324_0162, g32p_row17_traceSegment_078_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_078 0 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 0 324 324, g32p_row17_traceSegment_078_0000_0324, g32p_row17_traceSegment_078_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 648 10 10, g32p_row17_traceSegment_078_0648_0010, g32p_row17_traceSegment_078_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 668 10 10, g32p_row17_traceSegment_078_0668_0010, g32p_row17_traceSegment_078_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 648 20 20, g32p_row17_traceSegment_078_0648_0020, g32p_row17_traceSegment_078_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 688 10 10, g32p_row17_traceSegment_078_0688_0010, g32p_row17_traceSegment_078_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 708 10 11, g32p_row17_traceSegment_078_0708_0010, g32p_row17_traceSegment_078_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 688 20 21, g32p_row17_traceSegment_078_0688_0020, g32p_row17_traceSegment_078_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 648 40 41, g32p_row17_traceSegment_078_0648_0040, g32p_row17_traceSegment_078_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 729 10 10, g32p_row17_traceSegment_078_0729_0010, g32p_row17_traceSegment_078_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 749 10 10, g32p_row17_traceSegment_078_0749_0010, g32p_row17_traceSegment_078_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 729 20 20, g32p_row17_traceSegment_078_0729_0020, g32p_row17_traceSegment_078_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 769 10 10, g32p_row17_traceSegment_078_0769_0010, g32p_row17_traceSegment_078_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 789 10 11, g32p_row17_traceSegment_078_0789_0010, g32p_row17_traceSegment_078_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 769 20 21, g32p_row17_traceSegment_078_0769_0020, g32p_row17_traceSegment_078_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 729 40 41, g32p_row17_traceSegment_078_0729_0040, g32p_row17_traceSegment_078_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_078 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 648 81 81, g32p_row17_traceSegment_078_0648_0081, g32p_row17_traceSegment_078_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 810 10 10, g32p_row17_traceSegment_078_0810_0010, g32p_row17_traceSegment_078_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 830 10 10, g32p_row17_traceSegment_078_0830_0010, g32p_row17_traceSegment_078_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 810 20 20, g32p_row17_traceSegment_078_0810_0020, g32p_row17_traceSegment_078_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 850 10 10, g32p_row17_traceSegment_078_0850_0010, g32p_row17_traceSegment_078_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 870 10 11, g32p_row17_traceSegment_078_0870_0010, g32p_row17_traceSegment_078_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 850 20 21, g32p_row17_traceSegment_078_0850_0020, g32p_row17_traceSegment_078_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 810 40 41, g32p_row17_traceSegment_078_0810_0040, g32p_row17_traceSegment_078_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 891 10 10, g32p_row17_traceSegment_078_0891_0010, g32p_row17_traceSegment_078_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 911 10 10, g32p_row17_traceSegment_078_0911_0010, g32p_row17_traceSegment_078_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 891 20 20, g32p_row17_traceSegment_078_0891_0020, g32p_row17_traceSegment_078_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 931 10 10, g32p_row17_traceSegment_078_0931_0010, g32p_row17_traceSegment_078_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 951 10 11, g32p_row17_traceSegment_078_0951_0010, g32p_row17_traceSegment_078_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 931 20 21, g32p_row17_traceSegment_078_0931_0020, g32p_row17_traceSegment_078_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 891 40 41, g32p_row17_traceSegment_078_0891_0040, g32p_row17_traceSegment_078_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_078 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 810 81 81, g32p_row17_traceSegment_078_0810_0081, g32p_row17_traceSegment_078_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_078 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 648 162 162, g32p_row17_traceSegment_078_0648_0162, g32p_row17_traceSegment_078_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 972 10 10, g32p_row17_traceSegment_078_0972_0010, g32p_row17_traceSegment_078_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 992 10 10, g32p_row17_traceSegment_078_0992_0010, g32p_row17_traceSegment_078_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 972 20 20, g32p_row17_traceSegment_078_0972_0020, g32p_row17_traceSegment_078_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1012 10 10, g32p_row17_traceSegment_078_1012_0010, g32p_row17_traceSegment_078_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1032 10 11, g32p_row17_traceSegment_078_1032_0010, g32p_row17_traceSegment_078_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1012 20 21, g32p_row17_traceSegment_078_1012_0020, g32p_row17_traceSegment_078_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 972 40 41, g32p_row17_traceSegment_078_0972_0040, g32p_row17_traceSegment_078_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1063 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 1053 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1053 10 10, g32p_row17_traceSegment_078_1053_0010, g32p_row17_traceSegment_078_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1073 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 1073 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1073 10 10, g32p_row17_traceSegment_078_1073_0010, g32p_row17_traceSegment_078_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 1053 40 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1053 20 20, g32p_row17_traceSegment_078_1053_0020, g32p_row17_traceSegment_078_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1093 10 10, g32p_row17_traceSegment_078_1093_0010, g32p_row17_traceSegment_078_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1113 10 11, g32p_row17_traceSegment_078_1113_0010, g32p_row17_traceSegment_078_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1093 20 21, g32p_row17_traceSegment_078_1093_0020, g32p_row17_traceSegment_078_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 1053 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1053 40 41, g32p_row17_traceSegment_078_1053_0040, g32p_row17_traceSegment_078_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_078 972 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 972 81 81, g32p_row17_traceSegment_078_0972_0081, g32p_row17_traceSegment_078_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1144 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 1134 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1134 10 10, g32p_row17_traceSegment_078_1134_0010, g32p_row17_traceSegment_078_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1164 10 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 1154 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1154 10 10, g32p_row17_traceSegment_078_1154_0010, g32p_row17_traceSegment_078_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 1134 40 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1134 20 20, g32p_row17_traceSegment_078_1134_0020, g32p_row17_traceSegment_078_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1184 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 1174 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1174 10 10, g32p_row17_traceSegment_078_1174_0010, g32p_row17_traceSegment_078_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1194 10 11, g32p_row17_traceSegment_078_1194_0010, g32p_row17_traceSegment_078_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 1174 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1174 20 21, g32p_row17_traceSegment_078_1174_0020, g32p_row17_traceSegment_078_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 1134 81 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1134 40 41, g32p_row17_traceSegment_078_1134_0040, g32p_row17_traceSegment_078_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1215 10 10, g32p_row17_traceSegment_078_1215_0010, g32p_row17_traceSegment_078_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1235 10 10, g32p_row17_traceSegment_078_1235_0010, g32p_row17_traceSegment_078_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_078 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1215 20 20, g32p_row17_traceSegment_078_1215_0020, g32p_row17_traceSegment_078_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_078 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1255 10 10, g32p_row17_traceSegment_078_1255_0010, g32p_row17_traceSegment_078_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_078 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_078 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_078_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_078 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1275 10 11, g32p_row17_traceSegment_078_1275_0010, g32p_row17_traceSegment_078_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_078 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1255 20 21, g32p_row17_traceSegment_078_1255_0020, g32p_row17_traceSegment_078_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_078 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1215 40 41, g32p_row17_traceSegment_078_1215_0040, g32p_row17_traceSegment_078_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_078_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_078 1134 162 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 1134 81 81, g32p_row17_traceSegment_078_1134_0081, g32p_row17_traceSegment_078_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_078 972 324 = [6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 972 162 162, g32p_row17_traceSegment_078_0972_0162, g32p_row17_traceSegment_078_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_078 648 648 = [6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 648 324 324, g32p_row17_traceSegment_078_0648_0324, g32p_row17_traceSegment_078_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_078_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_078 0 1296 = [6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_078 0 648 648, g32p_row17_traceSegment_078_0000_0648, g32p_row17_traceSegment_078_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 78 = [6] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_078_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_079 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 79 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_079_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 0 10 10, g32p_row17_traceSegment_079_0000_0010, g32p_row17_traceSegment_079_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 20 10 10, g32p_row17_traceSegment_079_0020_0010, g32p_row17_traceSegment_079_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 0 20 20, g32p_row17_traceSegment_079_0000_0020, g32p_row17_traceSegment_079_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 40 10 10, g32p_row17_traceSegment_079_0040_0010, g32p_row17_traceSegment_079_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 60 10 11, g32p_row17_traceSegment_079_0060_0010, g32p_row17_traceSegment_079_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 40 20 21, g32p_row17_traceSegment_079_0040_0020, g32p_row17_traceSegment_079_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 0 40 41, g32p_row17_traceSegment_079_0000_0040, g32p_row17_traceSegment_079_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 81 10 10, g32p_row17_traceSegment_079_0081_0010, g32p_row17_traceSegment_079_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 101 10 10, g32p_row17_traceSegment_079_0101_0010, g32p_row17_traceSegment_079_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 81 20 20, g32p_row17_traceSegment_079_0081_0020, g32p_row17_traceSegment_079_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 121 10 10, g32p_row17_traceSegment_079_0121_0010, g32p_row17_traceSegment_079_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 141 10 11, g32p_row17_traceSegment_079_0141_0010, g32p_row17_traceSegment_079_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 121 20 21, g32p_row17_traceSegment_079_0121_0020, g32p_row17_traceSegment_079_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 81 40 41, g32p_row17_traceSegment_079_0081_0040, g32p_row17_traceSegment_079_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_079 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 0 81 81, g32p_row17_traceSegment_079_0000_0081, g32p_row17_traceSegment_079_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 162 10 10, g32p_row17_traceSegment_079_0162_0010, g32p_row17_traceSegment_079_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 182 10 10, g32p_row17_traceSegment_079_0182_0010, g32p_row17_traceSegment_079_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 162 20 20, g32p_row17_traceSegment_079_0162_0020, g32p_row17_traceSegment_079_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 202 10 10, g32p_row17_traceSegment_079_0202_0010, g32p_row17_traceSegment_079_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 232 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 222 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 222 10 11, g32p_row17_traceSegment_079_0222_0010, g32p_row17_traceSegment_079_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 202 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 202 20 21, g32p_row17_traceSegment_079_0202_0020, g32p_row17_traceSegment_079_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 162 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 162 40 41, g32p_row17_traceSegment_079_0162_0040, g32p_row17_traceSegment_079_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 243 10 10, g32p_row17_traceSegment_079_0243_0010, g32p_row17_traceSegment_079_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 263 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 263 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 263 10 10, g32p_row17_traceSegment_079_0263_0010, g32p_row17_traceSegment_079_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 243 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 243 20 20, g32p_row17_traceSegment_079_0243_0020, g32p_row17_traceSegment_079_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 283 10 10, g32p_row17_traceSegment_079_0283_0010, g32p_row17_traceSegment_079_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 303 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 313 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 303 21 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 303 10 11, g32p_row17_traceSegment_079_0303_0010, g32p_row17_traceSegment_079_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 283 41 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 283 20 21, g32p_row17_traceSegment_079_0283_0020, g32p_row17_traceSegment_079_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 243 81 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 243 40 41, g32p_row17_traceSegment_079_0243_0040, g32p_row17_traceSegment_079_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_079 162 162 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 162 81 81, g32p_row17_traceSegment_079_0162_0081, g32p_row17_traceSegment_079_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_079 0 324 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 0 162 162, g32p_row17_traceSegment_079_0000_0162, g32p_row17_traceSegment_079_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 334 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 324 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 324 10 10, g32p_row17_traceSegment_079_0324_0010, g32p_row17_traceSegment_079_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 344 10 10, g32p_row17_traceSegment_079_0344_0010, g32p_row17_traceSegment_079_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 324 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 324 20 20, g32p_row17_traceSegment_079_0324_0020, g32p_row17_traceSegment_079_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 364 10 10, g32p_row17_traceSegment_079_0364_0010, g32p_row17_traceSegment_079_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 384 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 384 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 384 10 11, g32p_row17_traceSegment_079_0384_0010, g32p_row17_traceSegment_079_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 364 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 364 20 21, g32p_row17_traceSegment_079_0364_0020, g32p_row17_traceSegment_079_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 324 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 324 40 41, g32p_row17_traceSegment_079_0324_0040, g32p_row17_traceSegment_079_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 405 10 10, g32p_row17_traceSegment_079_0405_0010, g32p_row17_traceSegment_079_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 435 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 425 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 425 10 10, g32p_row17_traceSegment_079_0425_0010, g32p_row17_traceSegment_079_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 405 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 405 20 20, g32p_row17_traceSegment_079_0405_0020, g32p_row17_traceSegment_079_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 445 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 445 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 445 10 10, g32p_row17_traceSegment_079_0445_0010, g32p_row17_traceSegment_079_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 465 10 11, g32p_row17_traceSegment_079_0465_0010, g32p_row17_traceSegment_079_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 445 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 445 20 21, g32p_row17_traceSegment_079_0445_0020, g32p_row17_traceSegment_079_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 405 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 405 40 41, g32p_row17_traceSegment_079_0405_0040, g32p_row17_traceSegment_079_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_079 324 162 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 324 81 81, g32p_row17_traceSegment_079_0324_0081, g32p_row17_traceSegment_079_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 486 10 10, g32p_row17_traceSegment_079_0486_0010, g32p_row17_traceSegment_079_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 506 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 506 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 506 10 10, g32p_row17_traceSegment_079_0506_0010, g32p_row17_traceSegment_079_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 486 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 486 20 20, g32p_row17_traceSegment_079_0486_0020, g32p_row17_traceSegment_079_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 526 10 10, g32p_row17_traceSegment_079_0526_0010, g32p_row17_traceSegment_079_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 546 10 11, g32p_row17_traceSegment_079_0546_0010, g32p_row17_traceSegment_079_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 526 20 21, g32p_row17_traceSegment_079_0526_0020, g32p_row17_traceSegment_079_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 486 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 486 40 41, g32p_row17_traceSegment_079_0486_0040, g32p_row17_traceSegment_079_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 567 10 10, g32p_row17_traceSegment_079_0567_0010, g32p_row17_traceSegment_079_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 587 10 10, g32p_row17_traceSegment_079_0587_0010, g32p_row17_traceSegment_079_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 567 20 20, g32p_row17_traceSegment_079_0567_0020, g32p_row17_traceSegment_079_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 607 10 10, g32p_row17_traceSegment_079_0607_0010, g32p_row17_traceSegment_079_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 627 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 627 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 627 10 11, g32p_row17_traceSegment_079_0627_0010, g32p_row17_traceSegment_079_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 607 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 607 20 21, g32p_row17_traceSegment_079_0607_0020, g32p_row17_traceSegment_079_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 567 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 567 40 41, g32p_row17_traceSegment_079_0567_0040, g32p_row17_traceSegment_079_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_079 486 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 486 81 81, g32p_row17_traceSegment_079_0486_0081, g32p_row17_traceSegment_079_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_079 324 324 = [6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 324 162 162, g32p_row17_traceSegment_079_0324_0162, g32p_row17_traceSegment_079_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_079 0 648 = [10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 0 324 324, g32p_row17_traceSegment_079_0000_0324, g32p_row17_traceSegment_079_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 648 10 10, g32p_row17_traceSegment_079_0648_0010, g32p_row17_traceSegment_079_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 668 10 10, g32p_row17_traceSegment_079_0668_0010, g32p_row17_traceSegment_079_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 648 20 20, g32p_row17_traceSegment_079_0648_0020, g32p_row17_traceSegment_079_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 688 10 10, g32p_row17_traceSegment_079_0688_0010, g32p_row17_traceSegment_079_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 708 10 11, g32p_row17_traceSegment_079_0708_0010, g32p_row17_traceSegment_079_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 688 20 21, g32p_row17_traceSegment_079_0688_0020, g32p_row17_traceSegment_079_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 648 40 41, g32p_row17_traceSegment_079_0648_0040, g32p_row17_traceSegment_079_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 729 10 10, g32p_row17_traceSegment_079_0729_0010, g32p_row17_traceSegment_079_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 749 10 10, g32p_row17_traceSegment_079_0749_0010, g32p_row17_traceSegment_079_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 729 20 20, g32p_row17_traceSegment_079_0729_0020, g32p_row17_traceSegment_079_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 769 10 10, g32p_row17_traceSegment_079_0769_0010, g32p_row17_traceSegment_079_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 789 10 11, g32p_row17_traceSegment_079_0789_0010, g32p_row17_traceSegment_079_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 769 20 21, g32p_row17_traceSegment_079_0769_0020, g32p_row17_traceSegment_079_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 729 40 41, g32p_row17_traceSegment_079_0729_0040, g32p_row17_traceSegment_079_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_079 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 648 81 81, g32p_row17_traceSegment_079_0648_0081, g32p_row17_traceSegment_079_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 810 10 10, g32p_row17_traceSegment_079_0810_0010, g32p_row17_traceSegment_079_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 830 10 10, g32p_row17_traceSegment_079_0830_0010, g32p_row17_traceSegment_079_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 810 20 20, g32p_row17_traceSegment_079_0810_0020, g32p_row17_traceSegment_079_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 850 10 10, g32p_row17_traceSegment_079_0850_0010, g32p_row17_traceSegment_079_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 870 10 11, g32p_row17_traceSegment_079_0870_0010, g32p_row17_traceSegment_079_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 850 20 21, g32p_row17_traceSegment_079_0850_0020, g32p_row17_traceSegment_079_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 810 40 41, g32p_row17_traceSegment_079_0810_0040, g32p_row17_traceSegment_079_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 901 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 891 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 891 10 10, g32p_row17_traceSegment_079_0891_0010, g32p_row17_traceSegment_079_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 911 10 10, g32p_row17_traceSegment_079_0911_0010, g32p_row17_traceSegment_079_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 891 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 891 20 20, g32p_row17_traceSegment_079_0891_0020, g32p_row17_traceSegment_079_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 931 10 10, g32p_row17_traceSegment_079_0931_0010, g32p_row17_traceSegment_079_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 951 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 951 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 951 10 11, g32p_row17_traceSegment_079_0951_0010, g32p_row17_traceSegment_079_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 931 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 931 20 21, g32p_row17_traceSegment_079_0931_0020, g32p_row17_traceSegment_079_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 891 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 891 40 41, g32p_row17_traceSegment_079_0891_0040, g32p_row17_traceSegment_079_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_079 810 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 810 81 81, g32p_row17_traceSegment_079_0810_0081, g32p_row17_traceSegment_079_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_079 648 324 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 648 162 162, g32p_row17_traceSegment_079_0648_0162, g32p_row17_traceSegment_079_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 972 10 10, g32p_row17_traceSegment_079_0972_0010, g32p_row17_traceSegment_079_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 992 10 10, g32p_row17_traceSegment_079_0992_0010, g32p_row17_traceSegment_079_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 972 20 20, g32p_row17_traceSegment_079_0972_0020, g32p_row17_traceSegment_079_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1012 10 10, g32p_row17_traceSegment_079_1012_0010, g32p_row17_traceSegment_079_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1032 10 11, g32p_row17_traceSegment_079_1032_0010, g32p_row17_traceSegment_079_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1012 20 21, g32p_row17_traceSegment_079_1012_0020, g32p_row17_traceSegment_079_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 972 40 41, g32p_row17_traceSegment_079_0972_0040, g32p_row17_traceSegment_079_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1053 10 10, g32p_row17_traceSegment_079_1053_0010, g32p_row17_traceSegment_079_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1073 10 10, g32p_row17_traceSegment_079_1073_0010, g32p_row17_traceSegment_079_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1053 20 20, g32p_row17_traceSegment_079_1053_0020, g32p_row17_traceSegment_079_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1093 10 10, g32p_row17_traceSegment_079_1093_0010, g32p_row17_traceSegment_079_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1113 10 11, g32p_row17_traceSegment_079_1113_0010, g32p_row17_traceSegment_079_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1093 20 21, g32p_row17_traceSegment_079_1093_0020, g32p_row17_traceSegment_079_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1053 40 41, g32p_row17_traceSegment_079_1053_0040, g32p_row17_traceSegment_079_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_079 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 972 81 81, g32p_row17_traceSegment_079_0972_0081, g32p_row17_traceSegment_079_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1134 10 10, g32p_row17_traceSegment_079_1134_0010, g32p_row17_traceSegment_079_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1154 10 10, g32p_row17_traceSegment_079_1154_0010, g32p_row17_traceSegment_079_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1134 20 20, g32p_row17_traceSegment_079_1134_0020, g32p_row17_traceSegment_079_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1174 10 10, g32p_row17_traceSegment_079_1174_0010, g32p_row17_traceSegment_079_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1194 10 11, g32p_row17_traceSegment_079_1194_0010, g32p_row17_traceSegment_079_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1174 20 21, g32p_row17_traceSegment_079_1174_0020, g32p_row17_traceSegment_079_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1134 40 41, g32p_row17_traceSegment_079_1134_0040, g32p_row17_traceSegment_079_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1215 10 10, g32p_row17_traceSegment_079_1215_0010, g32p_row17_traceSegment_079_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1235 10 10, g32p_row17_traceSegment_079_1235_0010, g32p_row17_traceSegment_079_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_079 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1215 20 20, g32p_row17_traceSegment_079_1215_0020, g32p_row17_traceSegment_079_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_079 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1255 10 10, g32p_row17_traceSegment_079_1255_0010, g32p_row17_traceSegment_079_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_079 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_079 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_079_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_079 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1275 10 11, g32p_row17_traceSegment_079_1275_0010, g32p_row17_traceSegment_079_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_079 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1255 20 21, g32p_row17_traceSegment_079_1255_0020, g32p_row17_traceSegment_079_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_079 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1215 40 41, g32p_row17_traceSegment_079_1215_0040, g32p_row17_traceSegment_079_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_079_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_079 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 1134 81 81, g32p_row17_traceSegment_079_1134_0081, g32p_row17_traceSegment_079_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_079 972 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 972 162 162, g32p_row17_traceSegment_079_0972_0162, g32p_row17_traceSegment_079_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_079 648 648 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 648 324 324, g32p_row17_traceSegment_079_0648_0324, g32p_row17_traceSegment_079_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_079_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_079 0 1296 = [12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_079 0 648 648, g32p_row17_traceSegment_079_0000_0648, g32p_row17_traceSegment_079_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 79 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_079_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 69) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 69) (g32p_literalTraceValue 16 69)
      [1, -1, 1] [10368, 10368] = true := by
  rw [g32p_row17_traceCoefficients_069]
  decide +kernel

theorem g32p_row17_tracePolynomial_071 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 71) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 71) (g32p_literalTraceValue 16 71)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_071]
  decide +kernel

theorem g32p_row17_tracePolynomial_074 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 74) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 74) (g32p_literalTraceValue 16 74)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_074]
  decide +kernel

theorem g32p_row17_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 75) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 75) (g32p_literalTraceValue 16 75)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_075]
  decide +kernel

theorem g32p_row17_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 76) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 76) (g32p_literalTraceValue 16 76)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_076]
  decide +kernel

theorem g32p_row17_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 77) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 77) (g32p_literalTraceValue 16 77)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_077]
  decide +kernel

theorem g32p_row17_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 78) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 78) (g32p_literalTraceValue 16 78)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_078]
  decide +kernel

theorem g32p_row17_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 79) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 79) (g32p_literalTraceValue 16 79)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_079]
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

private def g32p_row17_traceSegment_081 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 81 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_081_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 0 10 10, g32p_row17_traceSegment_081_0000_0010, g32p_row17_traceSegment_081_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 20 10 10, g32p_row17_traceSegment_081_0020_0010, g32p_row17_traceSegment_081_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 0 20 20, g32p_row17_traceSegment_081_0000_0020, g32p_row17_traceSegment_081_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 40 10 10, g32p_row17_traceSegment_081_0040_0010, g32p_row17_traceSegment_081_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 60 10 11, g32p_row17_traceSegment_081_0060_0010, g32p_row17_traceSegment_081_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 40 20 21, g32p_row17_traceSegment_081_0040_0020, g32p_row17_traceSegment_081_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 0 40 41, g32p_row17_traceSegment_081_0000_0040, g32p_row17_traceSegment_081_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 81 10 10, g32p_row17_traceSegment_081_0081_0010, g32p_row17_traceSegment_081_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 101 10 10, g32p_row17_traceSegment_081_0101_0010, g32p_row17_traceSegment_081_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 81 20 20, g32p_row17_traceSegment_081_0081_0020, g32p_row17_traceSegment_081_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 121 10 10, g32p_row17_traceSegment_081_0121_0010, g32p_row17_traceSegment_081_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 141 10 11, g32p_row17_traceSegment_081_0141_0010, g32p_row17_traceSegment_081_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 121 20 21, g32p_row17_traceSegment_081_0121_0020, g32p_row17_traceSegment_081_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 81 40 41, g32p_row17_traceSegment_081_0081_0040, g32p_row17_traceSegment_081_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_081 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 0 81 81, g32p_row17_traceSegment_081_0000_0081, g32p_row17_traceSegment_081_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 162 10 10, g32p_row17_traceSegment_081_0162_0010, g32p_row17_traceSegment_081_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 182 10 10, g32p_row17_traceSegment_081_0182_0010, g32p_row17_traceSegment_081_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 162 20 20, g32p_row17_traceSegment_081_0162_0020, g32p_row17_traceSegment_081_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 202 10 10, g32p_row17_traceSegment_081_0202_0010, g32p_row17_traceSegment_081_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 222 10 11, g32p_row17_traceSegment_081_0222_0010, g32p_row17_traceSegment_081_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 202 20 21, g32p_row17_traceSegment_081_0202_0020, g32p_row17_traceSegment_081_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 162 40 41, g32p_row17_traceSegment_081_0162_0040, g32p_row17_traceSegment_081_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 243 10 10, g32p_row17_traceSegment_081_0243_0010, g32p_row17_traceSegment_081_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 263 10 10, g32p_row17_traceSegment_081_0263_0010, g32p_row17_traceSegment_081_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 243 20 20, g32p_row17_traceSegment_081_0243_0020, g32p_row17_traceSegment_081_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 283 10 10, g32p_row17_traceSegment_081_0283_0010, g32p_row17_traceSegment_081_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 303 10 11, g32p_row17_traceSegment_081_0303_0010, g32p_row17_traceSegment_081_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 283 20 21, g32p_row17_traceSegment_081_0283_0020, g32p_row17_traceSegment_081_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 243 40 41, g32p_row17_traceSegment_081_0243_0040, g32p_row17_traceSegment_081_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_081 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 162 81 81, g32p_row17_traceSegment_081_0162_0081, g32p_row17_traceSegment_081_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_081 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 0 162 162, g32p_row17_traceSegment_081_0000_0162, g32p_row17_traceSegment_081_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 324 10 10, g32p_row17_traceSegment_081_0324_0010, g32p_row17_traceSegment_081_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 344 10 10, g32p_row17_traceSegment_081_0344_0010, g32p_row17_traceSegment_081_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 324 20 20, g32p_row17_traceSegment_081_0324_0020, g32p_row17_traceSegment_081_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 364 10 10, g32p_row17_traceSegment_081_0364_0010, g32p_row17_traceSegment_081_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 384 10 11, g32p_row17_traceSegment_081_0384_0010, g32p_row17_traceSegment_081_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 364 20 21, g32p_row17_traceSegment_081_0364_0020, g32p_row17_traceSegment_081_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 324 40 41, g32p_row17_traceSegment_081_0324_0040, g32p_row17_traceSegment_081_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 405 10 10, g32p_row17_traceSegment_081_0405_0010, g32p_row17_traceSegment_081_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 425 10 10, g32p_row17_traceSegment_081_0425_0010, g32p_row17_traceSegment_081_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 405 20 20, g32p_row17_traceSegment_081_0405_0020, g32p_row17_traceSegment_081_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 445 10 10, g32p_row17_traceSegment_081_0445_0010, g32p_row17_traceSegment_081_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 465 10 11, g32p_row17_traceSegment_081_0465_0010, g32p_row17_traceSegment_081_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 445 20 21, g32p_row17_traceSegment_081_0445_0020, g32p_row17_traceSegment_081_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 405 40 41, g32p_row17_traceSegment_081_0405_0040, g32p_row17_traceSegment_081_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_081 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 324 81 81, g32p_row17_traceSegment_081_0324_0081, g32p_row17_traceSegment_081_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 486 10 10, g32p_row17_traceSegment_081_0486_0010, g32p_row17_traceSegment_081_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 506 10 10, g32p_row17_traceSegment_081_0506_0010, g32p_row17_traceSegment_081_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 486 20 20, g32p_row17_traceSegment_081_0486_0020, g32p_row17_traceSegment_081_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 526 10 10, g32p_row17_traceSegment_081_0526_0010, g32p_row17_traceSegment_081_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 546 10 11, g32p_row17_traceSegment_081_0546_0010, g32p_row17_traceSegment_081_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 526 20 21, g32p_row17_traceSegment_081_0526_0020, g32p_row17_traceSegment_081_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 486 40 41, g32p_row17_traceSegment_081_0486_0040, g32p_row17_traceSegment_081_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 567 10 10, g32p_row17_traceSegment_081_0567_0010, g32p_row17_traceSegment_081_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 587 10 10, g32p_row17_traceSegment_081_0587_0010, g32p_row17_traceSegment_081_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 567 20 20, g32p_row17_traceSegment_081_0567_0020, g32p_row17_traceSegment_081_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 607 10 10, g32p_row17_traceSegment_081_0607_0010, g32p_row17_traceSegment_081_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 627 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 627 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 627 10 11, g32p_row17_traceSegment_081_0627_0010, g32p_row17_traceSegment_081_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 607 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 607 20 21, g32p_row17_traceSegment_081_0607_0020, g32p_row17_traceSegment_081_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 567 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 567 40 41, g32p_row17_traceSegment_081_0567_0040, g32p_row17_traceSegment_081_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_081 486 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 486 81 81, g32p_row17_traceSegment_081_0486_0081, g32p_row17_traceSegment_081_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_081 324 324 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 324 162 162, g32p_row17_traceSegment_081_0324_0162, g32p_row17_traceSegment_081_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_081 0 648 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 0 324 324, g32p_row17_traceSegment_081_0000_0324, g32p_row17_traceSegment_081_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 648 10 10, g32p_row17_traceSegment_081_0648_0010, g32p_row17_traceSegment_081_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 668 10 10, g32p_row17_traceSegment_081_0668_0010, g32p_row17_traceSegment_081_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 648 20 20, g32p_row17_traceSegment_081_0648_0020, g32p_row17_traceSegment_081_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 688 10 10, g32p_row17_traceSegment_081_0688_0010, g32p_row17_traceSegment_081_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 708 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 708 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 708 10 11, g32p_row17_traceSegment_081_0708_0010, g32p_row17_traceSegment_081_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 688 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 688 20 21, g32p_row17_traceSegment_081_0688_0020, g32p_row17_traceSegment_081_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 648 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 648 40 41, g32p_row17_traceSegment_081_0648_0040, g32p_row17_traceSegment_081_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 739 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 729 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 729 10 10, g32p_row17_traceSegment_081_0729_0010, g32p_row17_traceSegment_081_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 759 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 749 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 749 10 10, g32p_row17_traceSegment_081_0749_0010, g32p_row17_traceSegment_081_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 729 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 729 20 20, g32p_row17_traceSegment_081_0729_0020, g32p_row17_traceSegment_081_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 769 10 10, g32p_row17_traceSegment_081_0769_0010, g32p_row17_traceSegment_081_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 789 10 11, g32p_row17_traceSegment_081_0789_0010, g32p_row17_traceSegment_081_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 769 20 21, g32p_row17_traceSegment_081_0769_0020, g32p_row17_traceSegment_081_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 729 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 729 40 41, g32p_row17_traceSegment_081_0729_0040, g32p_row17_traceSegment_081_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_081 648 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 648 81 81, g32p_row17_traceSegment_081_0648_0081, g32p_row17_traceSegment_081_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 810 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 810 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 810 10 10, g32p_row17_traceSegment_081_0810_0010, g32p_row17_traceSegment_081_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 830 10 10, g32p_row17_traceSegment_081_0830_0010, g32p_row17_traceSegment_081_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 810 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 810 20 20, g32p_row17_traceSegment_081_0810_0020, g32p_row17_traceSegment_081_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 850 10 10, g32p_row17_traceSegment_081_0850_0010, g32p_row17_traceSegment_081_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 880 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 870 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 870 10 11, g32p_row17_traceSegment_081_0870_0010, g32p_row17_traceSegment_081_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 850 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 850 20 21, g32p_row17_traceSegment_081_0850_0020, g32p_row17_traceSegment_081_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 810 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 810 40 41, g32p_row17_traceSegment_081_0810_0040, g32p_row17_traceSegment_081_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 891 10 10, g32p_row17_traceSegment_081_0891_0010, g32p_row17_traceSegment_081_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 911 10 10, g32p_row17_traceSegment_081_0911_0010, g32p_row17_traceSegment_081_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 891 20 20, g32p_row17_traceSegment_081_0891_0020, g32p_row17_traceSegment_081_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 931 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 931 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 931 10 10, g32p_row17_traceSegment_081_0931_0010, g32p_row17_traceSegment_081_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 951 10 11, g32p_row17_traceSegment_081_0951_0010, g32p_row17_traceSegment_081_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 931 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 931 20 21, g32p_row17_traceSegment_081_0931_0020, g32p_row17_traceSegment_081_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 891 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 891 40 41, g32p_row17_traceSegment_081_0891_0040, g32p_row17_traceSegment_081_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_081 810 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 810 81 81, g32p_row17_traceSegment_081_0810_0081, g32p_row17_traceSegment_081_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_081 648 324 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 648 162 162, g32p_row17_traceSegment_081_0648_0162, g32p_row17_traceSegment_081_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 972 10 10, g32p_row17_traceSegment_081_0972_0010, g32p_row17_traceSegment_081_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 992 10 10, g32p_row17_traceSegment_081_0992_0010, g32p_row17_traceSegment_081_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 972 20 20, g32p_row17_traceSegment_081_0972_0020, g32p_row17_traceSegment_081_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1012 10 10, g32p_row17_traceSegment_081_1012_0010, g32p_row17_traceSegment_081_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1032 10 11, g32p_row17_traceSegment_081_1032_0010, g32p_row17_traceSegment_081_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1012 20 21, g32p_row17_traceSegment_081_1012_0020, g32p_row17_traceSegment_081_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 972 40 41, g32p_row17_traceSegment_081_0972_0040, g32p_row17_traceSegment_081_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1053 10 10, g32p_row17_traceSegment_081_1053_0010, g32p_row17_traceSegment_081_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1073 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 1073 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1073 10 10, g32p_row17_traceSegment_081_1073_0010, g32p_row17_traceSegment_081_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 1053 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1053 20 20, g32p_row17_traceSegment_081_1053_0020, g32p_row17_traceSegment_081_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1093 10 10, g32p_row17_traceSegment_081_1093_0010, g32p_row17_traceSegment_081_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1113 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 1123 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 1113 21 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1113 10 11, g32p_row17_traceSegment_081_1113_0010, g32p_row17_traceSegment_081_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 1093 41 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1093 20 21, g32p_row17_traceSegment_081_1093_0020, g32p_row17_traceSegment_081_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 1053 81 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1053 40 41, g32p_row17_traceSegment_081_1053_0040, g32p_row17_traceSegment_081_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_081 972 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 972 81 81, g32p_row17_traceSegment_081_0972_0081, g32p_row17_traceSegment_081_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1134 10 10, g32p_row17_traceSegment_081_1134_0010, g32p_row17_traceSegment_081_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1164 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 1154 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1154 10 10, g32p_row17_traceSegment_081_1154_0010, g32p_row17_traceSegment_081_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 1134 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1134 20 20, g32p_row17_traceSegment_081_1134_0020, g32p_row17_traceSegment_081_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1174 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 1174 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1174 10 10, g32p_row17_traceSegment_081_1174_0010, g32p_row17_traceSegment_081_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1194 10 11, g32p_row17_traceSegment_081_1194_0010, g32p_row17_traceSegment_081_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 1174 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1174 20 21, g32p_row17_traceSegment_081_1174_0020, g32p_row17_traceSegment_081_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 1134 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1134 40 41, g32p_row17_traceSegment_081_1134_0040, g32p_row17_traceSegment_081_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1215 10 10, g32p_row17_traceSegment_081_1215_0010, g32p_row17_traceSegment_081_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1235 10 10, g32p_row17_traceSegment_081_1235_0010, g32p_row17_traceSegment_081_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_081 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1215 20 20, g32p_row17_traceSegment_081_1215_0020, g32p_row17_traceSegment_081_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_081 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1255 10 10, g32p_row17_traceSegment_081_1255_0010, g32p_row17_traceSegment_081_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_081 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_081 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_081_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_081 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1275 10 11, g32p_row17_traceSegment_081_1275_0010, g32p_row17_traceSegment_081_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_081 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1255 20 21, g32p_row17_traceSegment_081_1255_0020, g32p_row17_traceSegment_081_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_081 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1215 40 41, g32p_row17_traceSegment_081_1215_0040, g32p_row17_traceSegment_081_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_081_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_081 1134 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 1134 81 81, g32p_row17_traceSegment_081_1134_0081, g32p_row17_traceSegment_081_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_081 972 324 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 972 162 162, g32p_row17_traceSegment_081_0972_0162, g32p_row17_traceSegment_081_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_081 648 648 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 648 324 324, g32p_row17_traceSegment_081_0648_0324, g32p_row17_traceSegment_081_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_081_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_081 0 1296 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_081 0 648 648, g32p_row17_traceSegment_081_0000_0648, g32p_row17_traceSegment_081_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_081 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 81 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_081_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_082 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 82 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_082_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 0 10 10, g32p_row17_traceSegment_082_0000_0010, g32p_row17_traceSegment_082_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 20 10 10, g32p_row17_traceSegment_082_0020_0010, g32p_row17_traceSegment_082_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 0 20 20, g32p_row17_traceSegment_082_0000_0020, g32p_row17_traceSegment_082_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 40 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 40 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 40 10 10, g32p_row17_traceSegment_082_0040_0010, g32p_row17_traceSegment_082_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 60 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 60 21 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 60 10 11, g32p_row17_traceSegment_082_0060_0010, g32p_row17_traceSegment_082_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 40 41 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 40 20 21, g32p_row17_traceSegment_082_0040_0020, g32p_row17_traceSegment_082_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 0 81 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 0 40 41, g32p_row17_traceSegment_082_0000_0040, g32p_row17_traceSegment_082_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 81 10 10, g32p_row17_traceSegment_082_0081_0010, g32p_row17_traceSegment_082_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 101 10 10, g32p_row17_traceSegment_082_0101_0010, g32p_row17_traceSegment_082_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 81 20 20, g32p_row17_traceSegment_082_0081_0020, g32p_row17_traceSegment_082_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 121 10 10, g32p_row17_traceSegment_082_0121_0010, g32p_row17_traceSegment_082_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 141 10 11, g32p_row17_traceSegment_082_0141_0010, g32p_row17_traceSegment_082_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 121 20 21, g32p_row17_traceSegment_082_0121_0020, g32p_row17_traceSegment_082_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 81 40 41, g32p_row17_traceSegment_082_0081_0040, g32p_row17_traceSegment_082_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_082 0 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 0 81 81, g32p_row17_traceSegment_082_0000_0081, g32p_row17_traceSegment_082_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 162 10 10, g32p_row17_traceSegment_082_0162_0010, g32p_row17_traceSegment_082_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 182 10 10, g32p_row17_traceSegment_082_0182_0010, g32p_row17_traceSegment_082_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 162 20 20, g32p_row17_traceSegment_082_0162_0020, g32p_row17_traceSegment_082_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 202 10 10, g32p_row17_traceSegment_082_0202_0010, g32p_row17_traceSegment_082_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 222 10 11, g32p_row17_traceSegment_082_0222_0010, g32p_row17_traceSegment_082_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 202 20 21, g32p_row17_traceSegment_082_0202_0020, g32p_row17_traceSegment_082_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 162 40 41, g32p_row17_traceSegment_082_0162_0040, g32p_row17_traceSegment_082_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 243 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 253 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 243 20 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 243 10 10, g32p_row17_traceSegment_082_0243_0010, g32p_row17_traceSegment_082_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 263 10 10, g32p_row17_traceSegment_082_0263_0010, g32p_row17_traceSegment_082_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 243 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 243 20 20, g32p_row17_traceSegment_082_0243_0020, g32p_row17_traceSegment_082_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 283 10 10, g32p_row17_traceSegment_082_0283_0010, g32p_row17_traceSegment_082_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 303 10 11, g32p_row17_traceSegment_082_0303_0010, g32p_row17_traceSegment_082_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 283 20 21, g32p_row17_traceSegment_082_0283_0020, g32p_row17_traceSegment_082_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 243 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 243 40 41, g32p_row17_traceSegment_082_0243_0040, g32p_row17_traceSegment_082_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_082 162 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 162 81 81, g32p_row17_traceSegment_082_0162_0081, g32p_row17_traceSegment_082_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_082 0 324 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 0 162 162, g32p_row17_traceSegment_082_0000_0162, g32p_row17_traceSegment_082_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 324 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 324 20 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 324 10 10, g32p_row17_traceSegment_082_0324_0010, g32p_row17_traceSegment_082_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 354 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 344 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 344 10 10, g32p_row17_traceSegment_082_0344_0010, g32p_row17_traceSegment_082_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 324 40 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 324 20 20, g32p_row17_traceSegment_082_0324_0020, g32p_row17_traceSegment_082_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 364 10 10, g32p_row17_traceSegment_082_0364_0010, g32p_row17_traceSegment_082_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 394 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 384 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 384 10 11, g32p_row17_traceSegment_082_0384_0010, g32p_row17_traceSegment_082_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 364 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 364 20 21, g32p_row17_traceSegment_082_0364_0020, g32p_row17_traceSegment_082_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 324 81 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 324 40 41, g32p_row17_traceSegment_082_0324_0040, g32p_row17_traceSegment_082_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 405 10 10, g32p_row17_traceSegment_082_0405_0010, g32p_row17_traceSegment_082_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 425 10 10, g32p_row17_traceSegment_082_0425_0010, g32p_row17_traceSegment_082_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 405 20 20, g32p_row17_traceSegment_082_0405_0020, g32p_row17_traceSegment_082_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 445 10 10, g32p_row17_traceSegment_082_0445_0010, g32p_row17_traceSegment_082_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 465 10 11, g32p_row17_traceSegment_082_0465_0010, g32p_row17_traceSegment_082_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 445 20 21, g32p_row17_traceSegment_082_0445_0020, g32p_row17_traceSegment_082_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 405 40 41, g32p_row17_traceSegment_082_0405_0040, g32p_row17_traceSegment_082_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_082 324 162 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 324 81 81, g32p_row17_traceSegment_082_0324_0081, g32p_row17_traceSegment_082_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 486 10 10, g32p_row17_traceSegment_082_0486_0010, g32p_row17_traceSegment_082_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 506 10 10, g32p_row17_traceSegment_082_0506_0010, g32p_row17_traceSegment_082_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 486 20 20, g32p_row17_traceSegment_082_0486_0020, g32p_row17_traceSegment_082_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 536 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 526 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 526 10 10, g32p_row17_traceSegment_082_0526_0010, g32p_row17_traceSegment_082_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 546 10 11, g32p_row17_traceSegment_082_0546_0010, g32p_row17_traceSegment_082_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 526 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 526 20 21, g32p_row17_traceSegment_082_0526_0020, g32p_row17_traceSegment_082_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 486 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 486 40 41, g32p_row17_traceSegment_082_0486_0040, g32p_row17_traceSegment_082_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 567 10 10, g32p_row17_traceSegment_082_0567_0010, g32p_row17_traceSegment_082_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 587 10 10, g32p_row17_traceSegment_082_0587_0010, g32p_row17_traceSegment_082_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 567 20 20, g32p_row17_traceSegment_082_0567_0020, g32p_row17_traceSegment_082_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 607 10 10, g32p_row17_traceSegment_082_0607_0010, g32p_row17_traceSegment_082_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 637 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 627 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 627 10 11, g32p_row17_traceSegment_082_0627_0010, g32p_row17_traceSegment_082_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 607 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 607 20 21, g32p_row17_traceSegment_082_0607_0020, g32p_row17_traceSegment_082_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 567 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 567 40 41, g32p_row17_traceSegment_082_0567_0040, g32p_row17_traceSegment_082_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_082 486 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 486 81 81, g32p_row17_traceSegment_082_0486_0081, g32p_row17_traceSegment_082_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_082 324 324 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 324 162 162, g32p_row17_traceSegment_082_0324_0162, g32p_row17_traceSegment_082_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_082 0 648 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 0 324 324, g32p_row17_traceSegment_082_0000_0324, g32p_row17_traceSegment_082_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 648 10 10, g32p_row17_traceSegment_082_0648_0010, g32p_row17_traceSegment_082_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 668 10 10, g32p_row17_traceSegment_082_0668_0010, g32p_row17_traceSegment_082_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 648 20 20, g32p_row17_traceSegment_082_0648_0020, g32p_row17_traceSegment_082_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 688 10 10, g32p_row17_traceSegment_082_0688_0010, g32p_row17_traceSegment_082_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 708 10 11, g32p_row17_traceSegment_082_0708_0010, g32p_row17_traceSegment_082_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 688 20 21, g32p_row17_traceSegment_082_0688_0020, g32p_row17_traceSegment_082_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 648 40 41, g32p_row17_traceSegment_082_0648_0040, g32p_row17_traceSegment_082_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 729 10 10, g32p_row17_traceSegment_082_0729_0010, g32p_row17_traceSegment_082_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 749 10 10, g32p_row17_traceSegment_082_0749_0010, g32p_row17_traceSegment_082_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 729 20 20, g32p_row17_traceSegment_082_0729_0020, g32p_row17_traceSegment_082_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 769 10 10, g32p_row17_traceSegment_082_0769_0010, g32p_row17_traceSegment_082_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 789 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 789 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 789 10 11, g32p_row17_traceSegment_082_0789_0010, g32p_row17_traceSegment_082_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 769 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 769 20 21, g32p_row17_traceSegment_082_0769_0020, g32p_row17_traceSegment_082_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 729 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 729 40 41, g32p_row17_traceSegment_082_0729_0040, g32p_row17_traceSegment_082_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_082 648 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 648 81 81, g32p_row17_traceSegment_082_0648_0081, g32p_row17_traceSegment_082_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 810 10 10, g32p_row17_traceSegment_082_0810_0010, g32p_row17_traceSegment_082_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 830 10 10, g32p_row17_traceSegment_082_0830_0010, g32p_row17_traceSegment_082_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 810 20 20, g32p_row17_traceSegment_082_0810_0020, g32p_row17_traceSegment_082_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 850 10 10, g32p_row17_traceSegment_082_0850_0010, g32p_row17_traceSegment_082_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 870 10 11, g32p_row17_traceSegment_082_0870_0010, g32p_row17_traceSegment_082_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 850 20 21, g32p_row17_traceSegment_082_0850_0020, g32p_row17_traceSegment_082_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 810 40 41, g32p_row17_traceSegment_082_0810_0040, g32p_row17_traceSegment_082_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 891 10 10, g32p_row17_traceSegment_082_0891_0010, g32p_row17_traceSegment_082_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 911 10 10, g32p_row17_traceSegment_082_0911_0010, g32p_row17_traceSegment_082_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 891 20 20, g32p_row17_traceSegment_082_0891_0020, g32p_row17_traceSegment_082_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 931 10 10, g32p_row17_traceSegment_082_0931_0010, g32p_row17_traceSegment_082_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 951 10 11, g32p_row17_traceSegment_082_0951_0010, g32p_row17_traceSegment_082_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 931 20 21, g32p_row17_traceSegment_082_0931_0020, g32p_row17_traceSegment_082_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 891 40 41, g32p_row17_traceSegment_082_0891_0040, g32p_row17_traceSegment_082_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_082 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 810 81 81, g32p_row17_traceSegment_082_0810_0081, g32p_row17_traceSegment_082_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_082 648 324 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 648 162 162, g32p_row17_traceSegment_082_0648_0162, g32p_row17_traceSegment_082_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 972 10 10, g32p_row17_traceSegment_082_0972_0010, g32p_row17_traceSegment_082_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 992 10 10, g32p_row17_traceSegment_082_0992_0010, g32p_row17_traceSegment_082_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 972 20 20, g32p_row17_traceSegment_082_0972_0020, g32p_row17_traceSegment_082_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1012 10 10, g32p_row17_traceSegment_082_1012_0010, g32p_row17_traceSegment_082_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1032 10 11, g32p_row17_traceSegment_082_1032_0010, g32p_row17_traceSegment_082_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1012 20 21, g32p_row17_traceSegment_082_1012_0020, g32p_row17_traceSegment_082_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 972 40 41, g32p_row17_traceSegment_082_0972_0040, g32p_row17_traceSegment_082_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1053 10 10, g32p_row17_traceSegment_082_1053_0010, g32p_row17_traceSegment_082_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1073 10 10, g32p_row17_traceSegment_082_1073_0010, g32p_row17_traceSegment_082_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1053 20 20, g32p_row17_traceSegment_082_1053_0020, g32p_row17_traceSegment_082_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1093 10 10, g32p_row17_traceSegment_082_1093_0010, g32p_row17_traceSegment_082_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1113 10 11, g32p_row17_traceSegment_082_1113_0010, g32p_row17_traceSegment_082_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1093 20 21, g32p_row17_traceSegment_082_1093_0020, g32p_row17_traceSegment_082_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1053 40 41, g32p_row17_traceSegment_082_1053_0040, g32p_row17_traceSegment_082_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_082 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 972 81 81, g32p_row17_traceSegment_082_0972_0081, g32p_row17_traceSegment_082_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1134 10 10, g32p_row17_traceSegment_082_1134_0010, g32p_row17_traceSegment_082_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1154 10 10, g32p_row17_traceSegment_082_1154_0010, g32p_row17_traceSegment_082_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1134 20 20, g32p_row17_traceSegment_082_1134_0020, g32p_row17_traceSegment_082_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1174 10 10, g32p_row17_traceSegment_082_1174_0010, g32p_row17_traceSegment_082_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1194 10 11, g32p_row17_traceSegment_082_1194_0010, g32p_row17_traceSegment_082_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1174 20 21, g32p_row17_traceSegment_082_1174_0020, g32p_row17_traceSegment_082_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1134 40 41, g32p_row17_traceSegment_082_1134_0040, g32p_row17_traceSegment_082_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1215 10 10, g32p_row17_traceSegment_082_1215_0010, g32p_row17_traceSegment_082_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1235 10 10, g32p_row17_traceSegment_082_1235_0010, g32p_row17_traceSegment_082_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_082 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1215 20 20, g32p_row17_traceSegment_082_1215_0020, g32p_row17_traceSegment_082_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_082 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1255 10 10, g32p_row17_traceSegment_082_1255_0010, g32p_row17_traceSegment_082_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_082 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_082 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_082_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_082 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1275 10 11, g32p_row17_traceSegment_082_1275_0010, g32p_row17_traceSegment_082_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_082 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1255 20 21, g32p_row17_traceSegment_082_1255_0020, g32p_row17_traceSegment_082_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_082 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1215 40 41, g32p_row17_traceSegment_082_1215_0040, g32p_row17_traceSegment_082_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_082_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_082 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 1134 81 81, g32p_row17_traceSegment_082_1134_0081, g32p_row17_traceSegment_082_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_082 972 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 972 162 162, g32p_row17_traceSegment_082_0972_0162, g32p_row17_traceSegment_082_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_082 648 648 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 648 324 324, g32p_row17_traceSegment_082_0648_0324, g32p_row17_traceSegment_082_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_082_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_082 0 1296 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_082 0 648 648, g32p_row17_traceSegment_082_0000_0648, g32p_row17_traceSegment_082_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 82 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_082_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_084 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 84 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_084_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 10 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 0 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 0 10 10, g32p_row17_traceSegment_084_0000_0010, g32p_row17_traceSegment_084_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 20 10 10, g32p_row17_traceSegment_084_0020_0010, g32p_row17_traceSegment_084_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 0 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 0 20 20, g32p_row17_traceSegment_084_0000_0020, g32p_row17_traceSegment_084_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 40 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 40 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 40 10 10, g32p_row17_traceSegment_084_0040_0010, g32p_row17_traceSegment_084_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 60 10 11, g32p_row17_traceSegment_084_0060_0010, g32p_row17_traceSegment_084_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 40 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 40 20 21, g32p_row17_traceSegment_084_0040_0020, g32p_row17_traceSegment_084_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 0 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 0 40 41, g32p_row17_traceSegment_084_0000_0040, g32p_row17_traceSegment_084_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 81 10 10, g32p_row17_traceSegment_084_0081_0010, g32p_row17_traceSegment_084_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 101 10 10, g32p_row17_traceSegment_084_0101_0010, g32p_row17_traceSegment_084_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 81 20 20, g32p_row17_traceSegment_084_0081_0020, g32p_row17_traceSegment_084_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 121 10 10, g32p_row17_traceSegment_084_0121_0010, g32p_row17_traceSegment_084_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 141 10 11, g32p_row17_traceSegment_084_0141_0010, g32p_row17_traceSegment_084_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 121 20 21, g32p_row17_traceSegment_084_0121_0020, g32p_row17_traceSegment_084_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 81 40 41, g32p_row17_traceSegment_084_0081_0040, g32p_row17_traceSegment_084_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_084 0 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 0 81 81, g32p_row17_traceSegment_084_0000_0081, g32p_row17_traceSegment_084_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 172 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 162 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 162 10 10, g32p_row17_traceSegment_084_0162_0010, g32p_row17_traceSegment_084_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 182 10 10, g32p_row17_traceSegment_084_0182_0010, g32p_row17_traceSegment_084_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 162 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 162 20 20, g32p_row17_traceSegment_084_0162_0020, g32p_row17_traceSegment_084_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 212 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 202 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 202 10 10, g32p_row17_traceSegment_084_0202_0010, g32p_row17_traceSegment_084_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 232 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 222 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 222 10 11, g32p_row17_traceSegment_084_0222_0010, g32p_row17_traceSegment_084_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 202 41 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 202 20 21, g32p_row17_traceSegment_084_0202_0020, g32p_row17_traceSegment_084_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 162 81 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 162 40 41, g32p_row17_traceSegment_084_0162_0040, g32p_row17_traceSegment_084_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 243 10 10, g32p_row17_traceSegment_084_0243_0010, g32p_row17_traceSegment_084_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 263 10 10, g32p_row17_traceSegment_084_0263_0010, g32p_row17_traceSegment_084_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 243 20 20, g32p_row17_traceSegment_084_0243_0020, g32p_row17_traceSegment_084_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 283 10 10, g32p_row17_traceSegment_084_0283_0010, g32p_row17_traceSegment_084_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 303 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 303 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 303 10 11, g32p_row17_traceSegment_084_0303_0010, g32p_row17_traceSegment_084_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 283 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 283 20 21, g32p_row17_traceSegment_084_0283_0020, g32p_row17_traceSegment_084_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 243 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 243 40 41, g32p_row17_traceSegment_084_0243_0040, g32p_row17_traceSegment_084_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_084 162 162 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 162 81 81, g32p_row17_traceSegment_084_0162_0081, g32p_row17_traceSegment_084_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_084 0 324 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 0 162 162, g32p_row17_traceSegment_084_0000_0162, g32p_row17_traceSegment_084_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 324 10 10, g32p_row17_traceSegment_084_0324_0010, g32p_row17_traceSegment_084_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 344 10 10, g32p_row17_traceSegment_084_0344_0010, g32p_row17_traceSegment_084_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 324 20 20, g32p_row17_traceSegment_084_0324_0020, g32p_row17_traceSegment_084_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 364 10 10, g32p_row17_traceSegment_084_0364_0010, g32p_row17_traceSegment_084_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 384 10 11, g32p_row17_traceSegment_084_0384_0010, g32p_row17_traceSegment_084_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 364 20 21, g32p_row17_traceSegment_084_0364_0020, g32p_row17_traceSegment_084_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 324 40 41, g32p_row17_traceSegment_084_0324_0040, g32p_row17_traceSegment_084_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 405 10 10, g32p_row17_traceSegment_084_0405_0010, g32p_row17_traceSegment_084_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 425 10 10, g32p_row17_traceSegment_084_0425_0010, g32p_row17_traceSegment_084_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 405 20 20, g32p_row17_traceSegment_084_0405_0020, g32p_row17_traceSegment_084_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 445 10 10, g32p_row17_traceSegment_084_0445_0010, g32p_row17_traceSegment_084_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 465 10 11, g32p_row17_traceSegment_084_0465_0010, g32p_row17_traceSegment_084_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 445 20 21, g32p_row17_traceSegment_084_0445_0020, g32p_row17_traceSegment_084_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 405 40 41, g32p_row17_traceSegment_084_0405_0040, g32p_row17_traceSegment_084_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_084 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 324 81 81, g32p_row17_traceSegment_084_0324_0081, g32p_row17_traceSegment_084_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 486 10 10, g32p_row17_traceSegment_084_0486_0010, g32p_row17_traceSegment_084_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 506 10 10, g32p_row17_traceSegment_084_0506_0010, g32p_row17_traceSegment_084_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 486 20 20, g32p_row17_traceSegment_084_0486_0020, g32p_row17_traceSegment_084_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 526 10 10, g32p_row17_traceSegment_084_0526_0010, g32p_row17_traceSegment_084_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 546 10 11, g32p_row17_traceSegment_084_0546_0010, g32p_row17_traceSegment_084_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 526 20 21, g32p_row17_traceSegment_084_0526_0020, g32p_row17_traceSegment_084_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 486 40 41, g32p_row17_traceSegment_084_0486_0040, g32p_row17_traceSegment_084_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 567 10 10, g32p_row17_traceSegment_084_0567_0010, g32p_row17_traceSegment_084_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 587 10 10, g32p_row17_traceSegment_084_0587_0010, g32p_row17_traceSegment_084_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 567 20 20, g32p_row17_traceSegment_084_0567_0020, g32p_row17_traceSegment_084_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 617 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 607 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 607 10 10, g32p_row17_traceSegment_084_0607_0010, g32p_row17_traceSegment_084_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 627 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 627 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 627 10 11, g32p_row17_traceSegment_084_0627_0010, g32p_row17_traceSegment_084_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 607 41 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 607 20 21, g32p_row17_traceSegment_084_0607_0020, g32p_row17_traceSegment_084_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 567 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 567 40 41, g32p_row17_traceSegment_084_0567_0040, g32p_row17_traceSegment_084_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_084 486 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 486 81 81, g32p_row17_traceSegment_084_0486_0081, g32p_row17_traceSegment_084_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_084 324 324 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 324 162 162, g32p_row17_traceSegment_084_0324_0162, g32p_row17_traceSegment_084_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_084 0 648 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 0 324 324, g32p_row17_traceSegment_084_0000_0324, g32p_row17_traceSegment_084_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 658 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 648 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 648 10 10, g32p_row17_traceSegment_084_0648_0010, g32p_row17_traceSegment_084_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 668 10 10, g32p_row17_traceSegment_084_0668_0010, g32p_row17_traceSegment_084_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 648 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 648 20 20, g32p_row17_traceSegment_084_0648_0020, g32p_row17_traceSegment_084_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 688 10 10, g32p_row17_traceSegment_084_0688_0010, g32p_row17_traceSegment_084_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 708 10 11, g32p_row17_traceSegment_084_0708_0010, g32p_row17_traceSegment_084_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 688 20 21, g32p_row17_traceSegment_084_0688_0020, g32p_row17_traceSegment_084_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 648 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 648 40 41, g32p_row17_traceSegment_084_0648_0040, g32p_row17_traceSegment_084_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 729 10 10, g32p_row17_traceSegment_084_0729_0010, g32p_row17_traceSegment_084_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 749 10 10, g32p_row17_traceSegment_084_0749_0010, g32p_row17_traceSegment_084_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 729 20 20, g32p_row17_traceSegment_084_0729_0020, g32p_row17_traceSegment_084_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 769 10 10, g32p_row17_traceSegment_084_0769_0010, g32p_row17_traceSegment_084_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 789 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 789 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 789 10 11, g32p_row17_traceSegment_084_0789_0010, g32p_row17_traceSegment_084_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 769 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 769 20 21, g32p_row17_traceSegment_084_0769_0020, g32p_row17_traceSegment_084_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 729 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 729 40 41, g32p_row17_traceSegment_084_0729_0040, g32p_row17_traceSegment_084_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_084 648 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 648 81 81, g32p_row17_traceSegment_084_0648_0081, g32p_row17_traceSegment_084_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 810 10 10, g32p_row17_traceSegment_084_0810_0010, g32p_row17_traceSegment_084_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 830 10 10, g32p_row17_traceSegment_084_0830_0010, g32p_row17_traceSegment_084_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 810 20 20, g32p_row17_traceSegment_084_0810_0020, g32p_row17_traceSegment_084_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 850 10 10, g32p_row17_traceSegment_084_0850_0010, g32p_row17_traceSegment_084_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 870 10 11, g32p_row17_traceSegment_084_0870_0010, g32p_row17_traceSegment_084_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 850 20 21, g32p_row17_traceSegment_084_0850_0020, g32p_row17_traceSegment_084_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 810 40 41, g32p_row17_traceSegment_084_0810_0040, g32p_row17_traceSegment_084_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 891 10 10, g32p_row17_traceSegment_084_0891_0010, g32p_row17_traceSegment_084_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 911 10 10, g32p_row17_traceSegment_084_0911_0010, g32p_row17_traceSegment_084_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 891 20 20, g32p_row17_traceSegment_084_0891_0020, g32p_row17_traceSegment_084_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 931 10 10, g32p_row17_traceSegment_084_0931_0010, g32p_row17_traceSegment_084_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 951 10 11, g32p_row17_traceSegment_084_0951_0010, g32p_row17_traceSegment_084_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 931 20 21, g32p_row17_traceSegment_084_0931_0020, g32p_row17_traceSegment_084_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 891 40 41, g32p_row17_traceSegment_084_0891_0040, g32p_row17_traceSegment_084_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_084 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 810 81 81, g32p_row17_traceSegment_084_0810_0081, g32p_row17_traceSegment_084_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_084 648 324 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 648 162 162, g32p_row17_traceSegment_084_0648_0162, g32p_row17_traceSegment_084_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 972 10 10, g32p_row17_traceSegment_084_0972_0010, g32p_row17_traceSegment_084_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 992 10 10, g32p_row17_traceSegment_084_0992_0010, g32p_row17_traceSegment_084_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 972 20 20, g32p_row17_traceSegment_084_0972_0020, g32p_row17_traceSegment_084_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1012 10 10, g32p_row17_traceSegment_084_1012_0010, g32p_row17_traceSegment_084_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 1042 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 1032 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1032 10 11, g32p_row17_traceSegment_084_1032_0010, g32p_row17_traceSegment_084_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 1012 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1012 20 21, g32p_row17_traceSegment_084_1012_0020, g32p_row17_traceSegment_084_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 972 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 972 40 41, g32p_row17_traceSegment_084_0972_0040, g32p_row17_traceSegment_084_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1053 10 10, g32p_row17_traceSegment_084_1053_0010, g32p_row17_traceSegment_084_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1073 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 1073 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1073 10 10, g32p_row17_traceSegment_084_1073_0010, g32p_row17_traceSegment_084_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 1053 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1053 20 20, g32p_row17_traceSegment_084_1053_0020, g32p_row17_traceSegment_084_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1093 10 10, g32p_row17_traceSegment_084_1093_0010, g32p_row17_traceSegment_084_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1113 10 11, g32p_row17_traceSegment_084_1113_0010, g32p_row17_traceSegment_084_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1093 20 21, g32p_row17_traceSegment_084_1093_0020, g32p_row17_traceSegment_084_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 1053 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1053 40 41, g32p_row17_traceSegment_084_1053_0040, g32p_row17_traceSegment_084_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_084 972 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 972 81 81, g32p_row17_traceSegment_084_0972_0081, g32p_row17_traceSegment_084_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1134 10 10, g32p_row17_traceSegment_084_1134_0010, g32p_row17_traceSegment_084_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1154 10 10, g32p_row17_traceSegment_084_1154_0010, g32p_row17_traceSegment_084_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1134 20 20, g32p_row17_traceSegment_084_1134_0020, g32p_row17_traceSegment_084_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1174 10 10, g32p_row17_traceSegment_084_1174_0010, g32p_row17_traceSegment_084_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1194 10 11, g32p_row17_traceSegment_084_1194_0010, g32p_row17_traceSegment_084_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1174 20 21, g32p_row17_traceSegment_084_1174_0020, g32p_row17_traceSegment_084_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1134 40 41, g32p_row17_traceSegment_084_1134_0040, g32p_row17_traceSegment_084_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1215 10 10, g32p_row17_traceSegment_084_1215_0010, g32p_row17_traceSegment_084_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1235 10 10, g32p_row17_traceSegment_084_1235_0010, g32p_row17_traceSegment_084_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_084 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1215 20 20, g32p_row17_traceSegment_084_1215_0020, g32p_row17_traceSegment_084_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_084 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1255 10 10, g32p_row17_traceSegment_084_1255_0010, g32p_row17_traceSegment_084_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_084 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_084 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_084_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_084 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1275 10 11, g32p_row17_traceSegment_084_1275_0010, g32p_row17_traceSegment_084_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_084 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1255 20 21, g32p_row17_traceSegment_084_1255_0020, g32p_row17_traceSegment_084_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_084 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1215 40 41, g32p_row17_traceSegment_084_1215_0040, g32p_row17_traceSegment_084_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_084_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_084 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 1134 81 81, g32p_row17_traceSegment_084_1134_0081, g32p_row17_traceSegment_084_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_084 972 324 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 972 162 162, g32p_row17_traceSegment_084_0972_0162, g32p_row17_traceSegment_084_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_084 648 648 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 648 324 324, g32p_row17_traceSegment_084_0648_0324, g32p_row17_traceSegment_084_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_084_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_084 0 1296 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_084 0 648 648, g32p_row17_traceSegment_084_0000_0648, g32p_row17_traceSegment_084_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 84 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_084_0000_1296

end HodgeLean.Foundations.Program

end
end
