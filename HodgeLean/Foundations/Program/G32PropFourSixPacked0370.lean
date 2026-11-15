import HodgeLean.Foundations.Program.G32PropFourSixPacked0367
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_038 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 38 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_038_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 0 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 10 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 0 20 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 0 10 10, g32p_row17_traceSegment_038_0000_0010, g32p_row17_traceSegment_038_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 20 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 30 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 20 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 20 10 10, g32p_row17_traceSegment_038_0020_0010, g32p_row17_traceSegment_038_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 0 40 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 0 20 20, g32p_row17_traceSegment_038_0000_0020, g32p_row17_traceSegment_038_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 40 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 50 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 40 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 40 10 10, g32p_row17_traceSegment_038_0040_0010, g32p_row17_traceSegment_038_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 60 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 70 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 60 21 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 60 10 11, g32p_row17_traceSegment_038_0060_0010, g32p_row17_traceSegment_038_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 40 41 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 40 20 21, g32p_row17_traceSegment_038_0040_0020, g32p_row17_traceSegment_038_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 0 81 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 0 40 41, g32p_row17_traceSegment_038_0000_0040, g32p_row17_traceSegment_038_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 91 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 81 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 81 10 10, g32p_row17_traceSegment_038_0081_0010, g32p_row17_traceSegment_038_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 101 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 101 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 101 10 10, g32p_row17_traceSegment_038_0101_0010, g32p_row17_traceSegment_038_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 81 40 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 81 20 20, g32p_row17_traceSegment_038_0081_0020, g32p_row17_traceSegment_038_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 121 10 10, g32p_row17_traceSegment_038_0121_0010, g32p_row17_traceSegment_038_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 141 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 151 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 141 21 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 141 10 11, g32p_row17_traceSegment_038_0141_0010, g32p_row17_traceSegment_038_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 121 41 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 121 20 21, g32p_row17_traceSegment_038_0121_0020, g32p_row17_traceSegment_038_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 81 81 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 81 40 41, g32p_row17_traceSegment_038_0081_0040, g32p_row17_traceSegment_038_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_038 0 162 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 0 81 81, g32p_row17_traceSegment_038_0000_0081, g32p_row17_traceSegment_038_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 172 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 162 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 162 10 10, g32p_row17_traceSegment_038_0162_0010, g32p_row17_traceSegment_038_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 192 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 182 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 182 10 10, g32p_row17_traceSegment_038_0182_0010, g32p_row17_traceSegment_038_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 162 40 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 162 20 20, g32p_row17_traceSegment_038_0162_0020, g32p_row17_traceSegment_038_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 202 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 212 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 202 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 202 10 10, g32p_row17_traceSegment_038_0202_0010, g32p_row17_traceSegment_038_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 222 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 232 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 222 21 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 222 10 11, g32p_row17_traceSegment_038_0222_0010, g32p_row17_traceSegment_038_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 202 41 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 202 20 21, g32p_row17_traceSegment_038_0202_0020, g32p_row17_traceSegment_038_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 162 81 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 162 40 41, g32p_row17_traceSegment_038_0162_0040, g32p_row17_traceSegment_038_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 243 10 10, g32p_row17_traceSegment_038_0243_0010, g32p_row17_traceSegment_038_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 263 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 273 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 263 20 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 263 10 10, g32p_row17_traceSegment_038_0263_0010, g32p_row17_traceSegment_038_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 243 40 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 243 20 20, g32p_row17_traceSegment_038_0243_0020, g32p_row17_traceSegment_038_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 283 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 293 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 283 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 283 10 10, g32p_row17_traceSegment_038_0283_0010, g32p_row17_traceSegment_038_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 303 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 303 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 303 10 11, g32p_row17_traceSegment_038_0303_0010, g32p_row17_traceSegment_038_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 283 41 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 283 20 21, g32p_row17_traceSegment_038_0283_0020, g32p_row17_traceSegment_038_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 243 81 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 243 40 41, g32p_row17_traceSegment_038_0243_0040, g32p_row17_traceSegment_038_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_038 162 162 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 162 81 81, g32p_row17_traceSegment_038_0162_0081, g32p_row17_traceSegment_038_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_038 0 324 = [0, 0, 0, 25] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 0 162 162, g32p_row17_traceSegment_038_0000_0162, g32p_row17_traceSegment_038_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 324 10 10, g32p_row17_traceSegment_038_0324_0010, g32p_row17_traceSegment_038_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 344 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 344 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 344 10 10, g32p_row17_traceSegment_038_0344_0010, g32p_row17_traceSegment_038_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 324 40 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 324 20 20, g32p_row17_traceSegment_038_0324_0020, g32p_row17_traceSegment_038_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 374 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 364 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 364 10 10, g32p_row17_traceSegment_038_0364_0010, g32p_row17_traceSegment_038_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 394 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 384 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 384 10 11, g32p_row17_traceSegment_038_0384_0010, g32p_row17_traceSegment_038_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 364 41 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 364 20 21, g32p_row17_traceSegment_038_0364_0020, g32p_row17_traceSegment_038_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 324 81 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 324 40 41, g32p_row17_traceSegment_038_0324_0040, g32p_row17_traceSegment_038_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 405 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 415 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 405 20 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 405 10 10, g32p_row17_traceSegment_038_0405_0010, g32p_row17_traceSegment_038_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 425 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 435 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 425 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 425 10 10, g32p_row17_traceSegment_038_0425_0010, g32p_row17_traceSegment_038_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 405 40 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 405 20 20, g32p_row17_traceSegment_038_0405_0020, g32p_row17_traceSegment_038_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 445 10 10, g32p_row17_traceSegment_038_0445_0010, g32p_row17_traceSegment_038_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 465 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 465 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 465 10 11, g32p_row17_traceSegment_038_0465_0010, g32p_row17_traceSegment_038_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 445 41 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 445 20 21, g32p_row17_traceSegment_038_0445_0020, g32p_row17_traceSegment_038_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 405 81 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 405 40 41, g32p_row17_traceSegment_038_0405_0040, g32p_row17_traceSegment_038_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_038 324 162 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 324 81 81, g32p_row17_traceSegment_038_0324_0081, g32p_row17_traceSegment_038_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 486 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 496 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 486 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 486 10 10, g32p_row17_traceSegment_038_0486_0010, g32p_row17_traceSegment_038_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 516 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 506 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 506 10 10, g32p_row17_traceSegment_038_0506_0010, g32p_row17_traceSegment_038_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 486 40 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 486 20 20, g32p_row17_traceSegment_038_0486_0020, g32p_row17_traceSegment_038_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 526 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 536 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 526 20 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 526 10 10, g32p_row17_traceSegment_038_0526_0010, g32p_row17_traceSegment_038_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 546 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 556 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 546 21 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 546 10 11, g32p_row17_traceSegment_038_0546_0010, g32p_row17_traceSegment_038_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 526 41 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 526 20 21, g32p_row17_traceSegment_038_0526_0020, g32p_row17_traceSegment_038_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 486 81 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 486 40 41, g32p_row17_traceSegment_038_0486_0040, g32p_row17_traceSegment_038_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 577 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 567 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 567 10 10, g32p_row17_traceSegment_038_0567_0010, g32p_row17_traceSegment_038_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 587 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 587 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 587 10 10, g32p_row17_traceSegment_038_0587_0010, g32p_row17_traceSegment_038_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 567 40 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 567 20 20, g32p_row17_traceSegment_038_0567_0020, g32p_row17_traceSegment_038_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 607 10 10, g32p_row17_traceSegment_038_0607_0010, g32p_row17_traceSegment_038_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 637 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 627 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 627 10 11, g32p_row17_traceSegment_038_0627_0010, g32p_row17_traceSegment_038_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 607 41 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 607 20 21, g32p_row17_traceSegment_038_0607_0020, g32p_row17_traceSegment_038_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 567 81 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 567 40 41, g32p_row17_traceSegment_038_0567_0040, g32p_row17_traceSegment_038_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_038 486 162 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 486 81 81, g32p_row17_traceSegment_038_0486_0081, g32p_row17_traceSegment_038_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_038 324 324 = [0, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 324 162 162, g32p_row17_traceSegment_038_0324_0162, g32p_row17_traceSegment_038_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_038 0 648 = [0, 0, 0, 46] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 0 324 324, g32p_row17_traceSegment_038_0000_0324, g32p_row17_traceSegment_038_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 658 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 648 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 648 10 10, g32p_row17_traceSegment_038_0648_0010, g32p_row17_traceSegment_038_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 678 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 668 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 668 10 10, g32p_row17_traceSegment_038_0668_0010, g32p_row17_traceSegment_038_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 648 40 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 648 20 20, g32p_row17_traceSegment_038_0648_0020, g32p_row17_traceSegment_038_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 688 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 698 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 688 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 688 10 10, g32p_row17_traceSegment_038_0688_0010, g32p_row17_traceSegment_038_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 718 11 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 708 21 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 708 10 11, g32p_row17_traceSegment_038_0708_0010, g32p_row17_traceSegment_038_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 688 41 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 688 20 21, g32p_row17_traceSegment_038_0688_0020, g32p_row17_traceSegment_038_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 648 81 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 648 40 41, g32p_row17_traceSegment_038_0648_0040, g32p_row17_traceSegment_038_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 729 10 10, g32p_row17_traceSegment_038_0729_0010, g32p_row17_traceSegment_038_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 749 10 10, g32p_row17_traceSegment_038_0749_0010, g32p_row17_traceSegment_038_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 729 20 20, g32p_row17_traceSegment_038_0729_0020, g32p_row17_traceSegment_038_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 769 10 10, g32p_row17_traceSegment_038_0769_0010, g32p_row17_traceSegment_038_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 799 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 789 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 789 10 11, g32p_row17_traceSegment_038_0789_0010, g32p_row17_traceSegment_038_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 769 41 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 769 20 21, g32p_row17_traceSegment_038_0769_0020, g32p_row17_traceSegment_038_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 729 81 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 729 40 41, g32p_row17_traceSegment_038_0729_0040, g32p_row17_traceSegment_038_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_038 648 162 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 648 81 81, g32p_row17_traceSegment_038_0648_0081, g32p_row17_traceSegment_038_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 810 10 10, g32p_row17_traceSegment_038_0810_0010, g32p_row17_traceSegment_038_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 830 10 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 830 20 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 830 10 10, g32p_row17_traceSegment_038_0830_0010, g32p_row17_traceSegment_038_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 810 40 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 810 20 20, g32p_row17_traceSegment_038_0810_0020, g32p_row17_traceSegment_038_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 850 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 860 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 850 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 850 10 10, g32p_row17_traceSegment_038_0850_0010, g32p_row17_traceSegment_038_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 870 10 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 880 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 870 21 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 870 10 11, g32p_row17_traceSegment_038_0870_0010, g32p_row17_traceSegment_038_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 850 41 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 850 20 21, g32p_row17_traceSegment_038_0850_0020, g32p_row17_traceSegment_038_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 810 81 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 810 40 41, g32p_row17_traceSegment_038_0810_0040, g32p_row17_traceSegment_038_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 891 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 901 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 891 20 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 891 10 10, g32p_row17_traceSegment_038_0891_0010, g32p_row17_traceSegment_038_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 921 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 911 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 911 10 10, g32p_row17_traceSegment_038_0911_0010, g32p_row17_traceSegment_038_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 891 40 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 891 20 20, g32p_row17_traceSegment_038_0891_0020, g32p_row17_traceSegment_038_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 931 10 10, g32p_row17_traceSegment_038_0931_0010, g32p_row17_traceSegment_038_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 951 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 951 21 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 951 10 11, g32p_row17_traceSegment_038_0951_0010, g32p_row17_traceSegment_038_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 931 41 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 931 20 21, g32p_row17_traceSegment_038_0931_0020, g32p_row17_traceSegment_038_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 891 81 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 891 40 41, g32p_row17_traceSegment_038_0891_0040, g32p_row17_traceSegment_038_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_038 810 162 = [0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 810 81 81, g32p_row17_traceSegment_038_0810_0081, g32p_row17_traceSegment_038_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_038 648 324 = [0, 0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 648 162 162, g32p_row17_traceSegment_038_0648_0162, g32p_row17_traceSegment_038_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 972 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 982 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 972 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 972 10 10, g32p_row17_traceSegment_038_0972_0010, g32p_row17_traceSegment_038_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1002 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 992 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 992 10 10, g32p_row17_traceSegment_038_0992_0010, g32p_row17_traceSegment_038_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 972 40 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 972 20 20, g32p_row17_traceSegment_038_0972_0020, g32p_row17_traceSegment_038_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1012 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1022 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 1012 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1012 10 10, g32p_row17_traceSegment_038_1012_0010, g32p_row17_traceSegment_038_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1032 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 1032 21 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1032 10 11, g32p_row17_traceSegment_038_1032_0010, g32p_row17_traceSegment_038_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 1012 41 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1012 20 21, g32p_row17_traceSegment_038_1012_0020, g32p_row17_traceSegment_038_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 972 81 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 972 40 41, g32p_row17_traceSegment_038_0972_0040, g32p_row17_traceSegment_038_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1053 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1063 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 1053 20 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1053 10 10, g32p_row17_traceSegment_038_1053_0010, g32p_row17_traceSegment_038_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1073 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 1073 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1073 10 10, g32p_row17_traceSegment_038_1073_0010, g32p_row17_traceSegment_038_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 1053 40 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1053 20 20, g32p_row17_traceSegment_038_1053_0020, g32p_row17_traceSegment_038_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1093 10 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 1093 20 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1093 10 10, g32p_row17_traceSegment_038_1093_0010, g32p_row17_traceSegment_038_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1113 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 1123 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 1113 21 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1113 10 11, g32p_row17_traceSegment_038_1113_0010, g32p_row17_traceSegment_038_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 1093 41 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1093 20 21, g32p_row17_traceSegment_038_1093_0020, g32p_row17_traceSegment_038_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 1053 81 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1053 40 41, g32p_row17_traceSegment_038_1053_0040, g32p_row17_traceSegment_038_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_038 972 162 = [0, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 972 81 81, g32p_row17_traceSegment_038_0972_0081, g32p_row17_traceSegment_038_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1144 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 1134 20 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1134 10 10, g32p_row17_traceSegment_038_1134_0010, g32p_row17_traceSegment_038_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1154 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1164 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 1154 20 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1154 10 10, g32p_row17_traceSegment_038_1154_0010, g32p_row17_traceSegment_038_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 1134 40 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1134 20 20, g32p_row17_traceSegment_038_1134_0020, g32p_row17_traceSegment_038_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1174 10 10, g32p_row17_traceSegment_038_1174_0010, g32p_row17_traceSegment_038_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1194 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 1194 21 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1194 10 11, g32p_row17_traceSegment_038_1194_0010, g32p_row17_traceSegment_038_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 1174 41 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1174 20 21, g32p_row17_traceSegment_038_1174_0020, g32p_row17_traceSegment_038_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 1134 81 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1134 40 41, g32p_row17_traceSegment_038_1134_0040, g32p_row17_traceSegment_038_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1215 10 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1225 10 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 1215 20 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1215 10 10, g32p_row17_traceSegment_038_1215_0010, g32p_row17_traceSegment_038_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1235 10 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 1235 20 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1235 10 10, g32p_row17_traceSegment_038_1235_0010, g32p_row17_traceSegment_038_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_038 1215 40 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1215 20 20, g32p_row17_traceSegment_038_1215_0020, g32p_row17_traceSegment_038_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1255 10 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1265 10 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_038 1255 20 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1255 10 10, g32p_row17_traceSegment_038_1255_0010, g32p_row17_traceSegment_038_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_038 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_038 1285 11 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_038_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_038 1275 21 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1275 10 11, g32p_row17_traceSegment_038_1275_0010, g32p_row17_traceSegment_038_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_038 1255 41 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1255 20 21, g32p_row17_traceSegment_038_1255_0020, g32p_row17_traceSegment_038_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_038 1215 81 = [0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1215 40 41, g32p_row17_traceSegment_038_1215_0040, g32p_row17_traceSegment_038_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_038_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_038 1134 162 = [0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 1134 81 81, g32p_row17_traceSegment_038_1134_0081, g32p_row17_traceSegment_038_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_038 972 324 = [0, 0, 0, 39] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 972 162 162, g32p_row17_traceSegment_038_0972_0162, g32p_row17_traceSegment_038_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_038 648 648 = [0, 0, 0, 62] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 648 324 324, g32p_row17_traceSegment_038_0648_0324, g32p_row17_traceSegment_038_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_038_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_038 0 1296 = [0, 0, 0, 108] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_038 0 648 648, g32p_row17_traceSegment_038_0000_0648, g32p_row17_traceSegment_038_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_038 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 38 = [0, 0, 0, 108] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_038_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_040 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 40 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_040_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 0 10 10, g32p_row17_traceSegment_040_0000_0010, g32p_row17_traceSegment_040_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 20 10 10, g32p_row17_traceSegment_040_0020_0010, g32p_row17_traceSegment_040_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 0 20 20, g32p_row17_traceSegment_040_0000_0020, g32p_row17_traceSegment_040_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 40 10 10, g32p_row17_traceSegment_040_0040_0010, g32p_row17_traceSegment_040_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 70 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 60 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 60 10 11, g32p_row17_traceSegment_040_0060_0010, g32p_row17_traceSegment_040_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 40 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 40 20 21, g32p_row17_traceSegment_040_0040_0020, g32p_row17_traceSegment_040_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 0 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 0 40 41, g32p_row17_traceSegment_040_0000_0040, g32p_row17_traceSegment_040_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 91 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 81 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 81 10 10, g32p_row17_traceSegment_040_0081_0010, g32p_row17_traceSegment_040_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 101 10 10, g32p_row17_traceSegment_040_0101_0010, g32p_row17_traceSegment_040_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 81 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 81 20 20, g32p_row17_traceSegment_040_0081_0020, g32p_row17_traceSegment_040_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 121 10 10, g32p_row17_traceSegment_040_0121_0010, g32p_row17_traceSegment_040_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 141 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 141 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 141 10 11, g32p_row17_traceSegment_040_0141_0010, g32p_row17_traceSegment_040_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 121 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 121 20 21, g32p_row17_traceSegment_040_0121_0020, g32p_row17_traceSegment_040_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 81 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 81 40 41, g32p_row17_traceSegment_040_0081_0040, g32p_row17_traceSegment_040_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_040 0 162 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 0 81 81, g32p_row17_traceSegment_040_0000_0081, g32p_row17_traceSegment_040_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 162 10 10, g32p_row17_traceSegment_040_0162_0010, g32p_row17_traceSegment_040_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 182 10 10, g32p_row17_traceSegment_040_0182_0010, g32p_row17_traceSegment_040_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 162 20 20, g32p_row17_traceSegment_040_0162_0020, g32p_row17_traceSegment_040_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 202 10 10, g32p_row17_traceSegment_040_0202_0010, g32p_row17_traceSegment_040_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 222 10 11, g32p_row17_traceSegment_040_0222_0010, g32p_row17_traceSegment_040_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 202 20 21, g32p_row17_traceSegment_040_0202_0020, g32p_row17_traceSegment_040_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 162 40 41, g32p_row17_traceSegment_040_0162_0040, g32p_row17_traceSegment_040_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 243 10 10, g32p_row17_traceSegment_040_0243_0010, g32p_row17_traceSegment_040_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 263 10 10, g32p_row17_traceSegment_040_0263_0010, g32p_row17_traceSegment_040_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 243 20 20, g32p_row17_traceSegment_040_0243_0020, g32p_row17_traceSegment_040_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 283 10 10, g32p_row17_traceSegment_040_0283_0010, g32p_row17_traceSegment_040_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 303 10 11, g32p_row17_traceSegment_040_0303_0010, g32p_row17_traceSegment_040_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 283 20 21, g32p_row17_traceSegment_040_0283_0020, g32p_row17_traceSegment_040_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 243 40 41, g32p_row17_traceSegment_040_0243_0040, g32p_row17_traceSegment_040_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_040 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 162 81 81, g32p_row17_traceSegment_040_0162_0081, g32p_row17_traceSegment_040_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_040 0 324 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 0 162 162, g32p_row17_traceSegment_040_0000_0162, g32p_row17_traceSegment_040_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 324 10 10, g32p_row17_traceSegment_040_0324_0010, g32p_row17_traceSegment_040_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 344 10 10, g32p_row17_traceSegment_040_0344_0010, g32p_row17_traceSegment_040_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 324 20 20, g32p_row17_traceSegment_040_0324_0020, g32p_row17_traceSegment_040_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 364 10 10, g32p_row17_traceSegment_040_0364_0010, g32p_row17_traceSegment_040_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 384 10 11, g32p_row17_traceSegment_040_0384_0010, g32p_row17_traceSegment_040_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 364 20 21, g32p_row17_traceSegment_040_0364_0020, g32p_row17_traceSegment_040_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 324 40 41, g32p_row17_traceSegment_040_0324_0040, g32p_row17_traceSegment_040_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 405 10 10, g32p_row17_traceSegment_040_0405_0010, g32p_row17_traceSegment_040_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 425 10 10, g32p_row17_traceSegment_040_0425_0010, g32p_row17_traceSegment_040_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 405 20 20, g32p_row17_traceSegment_040_0405_0020, g32p_row17_traceSegment_040_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 445 10 10, g32p_row17_traceSegment_040_0445_0010, g32p_row17_traceSegment_040_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 465 10 11, g32p_row17_traceSegment_040_0465_0010, g32p_row17_traceSegment_040_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 445 20 21, g32p_row17_traceSegment_040_0445_0020, g32p_row17_traceSegment_040_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 405 40 41, g32p_row17_traceSegment_040_0405_0040, g32p_row17_traceSegment_040_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_040 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 324 81 81, g32p_row17_traceSegment_040_0324_0081, g32p_row17_traceSegment_040_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 486 10 10, g32p_row17_traceSegment_040_0486_0010, g32p_row17_traceSegment_040_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 506 10 10, g32p_row17_traceSegment_040_0506_0010, g32p_row17_traceSegment_040_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 486 20 20, g32p_row17_traceSegment_040_0486_0020, g32p_row17_traceSegment_040_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 526 10 10, g32p_row17_traceSegment_040_0526_0010, g32p_row17_traceSegment_040_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 546 10 11, g32p_row17_traceSegment_040_0546_0010, g32p_row17_traceSegment_040_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 526 20 21, g32p_row17_traceSegment_040_0526_0020, g32p_row17_traceSegment_040_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 486 40 41, g32p_row17_traceSegment_040_0486_0040, g32p_row17_traceSegment_040_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 567 10 10, g32p_row17_traceSegment_040_0567_0010, g32p_row17_traceSegment_040_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 587 10 10, g32p_row17_traceSegment_040_0587_0010, g32p_row17_traceSegment_040_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 567 20 20, g32p_row17_traceSegment_040_0567_0020, g32p_row17_traceSegment_040_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 607 10 10, g32p_row17_traceSegment_040_0607_0010, g32p_row17_traceSegment_040_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 627 10 11, g32p_row17_traceSegment_040_0627_0010, g32p_row17_traceSegment_040_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 607 20 21, g32p_row17_traceSegment_040_0607_0020, g32p_row17_traceSegment_040_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 567 40 41, g32p_row17_traceSegment_040_0567_0040, g32p_row17_traceSegment_040_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_040 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 486 81 81, g32p_row17_traceSegment_040_0486_0081, g32p_row17_traceSegment_040_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_040 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 324 162 162, g32p_row17_traceSegment_040_0324_0162, g32p_row17_traceSegment_040_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_040 0 648 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 0 324 324, g32p_row17_traceSegment_040_0000_0324, g32p_row17_traceSegment_040_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 648 10 10, g32p_row17_traceSegment_040_0648_0010, g32p_row17_traceSegment_040_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 668 10 10, g32p_row17_traceSegment_040_0668_0010, g32p_row17_traceSegment_040_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 648 20 20, g32p_row17_traceSegment_040_0648_0020, g32p_row17_traceSegment_040_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 698 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 688 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 688 10 10, g32p_row17_traceSegment_040_0688_0010, g32p_row17_traceSegment_040_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 708 10 11, g32p_row17_traceSegment_040_0708_0010, g32p_row17_traceSegment_040_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 688 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 688 20 21, g32p_row17_traceSegment_040_0688_0020, g32p_row17_traceSegment_040_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 648 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 648 40 41, g32p_row17_traceSegment_040_0648_0040, g32p_row17_traceSegment_040_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 739 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 729 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 729 10 10, g32p_row17_traceSegment_040_0729_0010, g32p_row17_traceSegment_040_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 749 10 10, g32p_row17_traceSegment_040_0749_0010, g32p_row17_traceSegment_040_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 729 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 729 20 20, g32p_row17_traceSegment_040_0729_0020, g32p_row17_traceSegment_040_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 769 10 10, g32p_row17_traceSegment_040_0769_0010, g32p_row17_traceSegment_040_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 789 10 11, g32p_row17_traceSegment_040_0789_0010, g32p_row17_traceSegment_040_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 769 20 21, g32p_row17_traceSegment_040_0769_0020, g32p_row17_traceSegment_040_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 729 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 729 40 41, g32p_row17_traceSegment_040_0729_0040, g32p_row17_traceSegment_040_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_040 648 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 648 81 81, g32p_row17_traceSegment_040_0648_0081, g32p_row17_traceSegment_040_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 810 10 10, g32p_row17_traceSegment_040_0810_0010, g32p_row17_traceSegment_040_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 830 10 10, g32p_row17_traceSegment_040_0830_0010, g32p_row17_traceSegment_040_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 810 20 20, g32p_row17_traceSegment_040_0810_0020, g32p_row17_traceSegment_040_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 850 10 10, g32p_row17_traceSegment_040_0850_0010, g32p_row17_traceSegment_040_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 880 11 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 870 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 870 10 11, g32p_row17_traceSegment_040_0870_0010, g32p_row17_traceSegment_040_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 850 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 850 20 21, g32p_row17_traceSegment_040_0850_0020, g32p_row17_traceSegment_040_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 810 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 810 40 41, g32p_row17_traceSegment_040_0810_0040, g32p_row17_traceSegment_040_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 891 10 10, g32p_row17_traceSegment_040_0891_0010, g32p_row17_traceSegment_040_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 911 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 911 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 911 10 10, g32p_row17_traceSegment_040_0911_0010, g32p_row17_traceSegment_040_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 891 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 891 20 20, g32p_row17_traceSegment_040_0891_0020, g32p_row17_traceSegment_040_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 931 10 10, g32p_row17_traceSegment_040_0931_0010, g32p_row17_traceSegment_040_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 951 10 11, g32p_row17_traceSegment_040_0951_0010, g32p_row17_traceSegment_040_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 931 20 21, g32p_row17_traceSegment_040_0931_0020, g32p_row17_traceSegment_040_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 891 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 891 40 41, g32p_row17_traceSegment_040_0891_0040, g32p_row17_traceSegment_040_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_040 810 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 810 81 81, g32p_row17_traceSegment_040_0810_0081, g32p_row17_traceSegment_040_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_040 648 324 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 648 162 162, g32p_row17_traceSegment_040_0648_0162, g32p_row17_traceSegment_040_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 972 10 10, g32p_row17_traceSegment_040_0972_0010, g32p_row17_traceSegment_040_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 992 10 10, g32p_row17_traceSegment_040_0992_0010, g32p_row17_traceSegment_040_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 972 20 20, g32p_row17_traceSegment_040_0972_0020, g32p_row17_traceSegment_040_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1012 10 10, g32p_row17_traceSegment_040_1012_0010, g32p_row17_traceSegment_040_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1032 10 11, g32p_row17_traceSegment_040_1032_0010, g32p_row17_traceSegment_040_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1012 20 21, g32p_row17_traceSegment_040_1012_0020, g32p_row17_traceSegment_040_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 972 40 41, g32p_row17_traceSegment_040_0972_0040, g32p_row17_traceSegment_040_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1053 10 10, g32p_row17_traceSegment_040_1053_0010, g32p_row17_traceSegment_040_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1073 10 10, g32p_row17_traceSegment_040_1073_0010, g32p_row17_traceSegment_040_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1053 20 20, g32p_row17_traceSegment_040_1053_0020, g32p_row17_traceSegment_040_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1093 10 10, g32p_row17_traceSegment_040_1093_0010, g32p_row17_traceSegment_040_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1113 10 11, g32p_row17_traceSegment_040_1113_0010, g32p_row17_traceSegment_040_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1093 20 21, g32p_row17_traceSegment_040_1093_0020, g32p_row17_traceSegment_040_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1053 40 41, g32p_row17_traceSegment_040_1053_0040, g32p_row17_traceSegment_040_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_040 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 972 81 81, g32p_row17_traceSegment_040_0972_0081, g32p_row17_traceSegment_040_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1134 10 10, g32p_row17_traceSegment_040_1134_0010, g32p_row17_traceSegment_040_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1164 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 1154 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1154 10 10, g32p_row17_traceSegment_040_1154_0010, g32p_row17_traceSegment_040_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 1134 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1134 20 20, g32p_row17_traceSegment_040_1134_0020, g32p_row17_traceSegment_040_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1174 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1184 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 1174 20 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1174 10 10, g32p_row17_traceSegment_040_1174_0010, g32p_row17_traceSegment_040_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1194 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 1194 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1194 10 11, g32p_row17_traceSegment_040_1194_0010, g32p_row17_traceSegment_040_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 1174 41 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1174 20 21, g32p_row17_traceSegment_040_1174_0020, g32p_row17_traceSegment_040_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 1134 81 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1134 40 41, g32p_row17_traceSegment_040_1134_0040, g32p_row17_traceSegment_040_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1215 10 10, g32p_row17_traceSegment_040_1215_0010, g32p_row17_traceSegment_040_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1235 10 10, g32p_row17_traceSegment_040_1235_0010, g32p_row17_traceSegment_040_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_040 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1215 20 20, g32p_row17_traceSegment_040_1215_0020, g32p_row17_traceSegment_040_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1255 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_040 1255 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1255 10 10, g32p_row17_traceSegment_040_1255_0010, g32p_row17_traceSegment_040_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_040 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_040 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_040_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_040 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1275 10 11, g32p_row17_traceSegment_040_1275_0010, g32p_row17_traceSegment_040_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_040 1255 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1255 20 21, g32p_row17_traceSegment_040_1255_0020, g32p_row17_traceSegment_040_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_040 1215 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1215 40 41, g32p_row17_traceSegment_040_1215_0040, g32p_row17_traceSegment_040_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_040_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_040 1134 162 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 1134 81 81, g32p_row17_traceSegment_040_1134_0081, g32p_row17_traceSegment_040_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_040 972 324 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 972 162 162, g32p_row17_traceSegment_040_0972_0162, g32p_row17_traceSegment_040_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_040 648 648 = [9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 648 324 324, g32p_row17_traceSegment_040_0648_0324, g32p_row17_traceSegment_040_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_040_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_040 0 1296 = [12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_040 0 648 648, g32p_row17_traceSegment_040_0000_0648, g32p_row17_traceSegment_040_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_040 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 40 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_040_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_043 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 43 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_043_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 0 10 10, g32p_row17_traceSegment_043_0000_0010, g32p_row17_traceSegment_043_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 20 10 10, g32p_row17_traceSegment_043_0020_0010, g32p_row17_traceSegment_043_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 0 20 20, g32p_row17_traceSegment_043_0000_0020, g32p_row17_traceSegment_043_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 40 10 10, g32p_row17_traceSegment_043_0040_0010, g32p_row17_traceSegment_043_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 60 10 11, g32p_row17_traceSegment_043_0060_0010, g32p_row17_traceSegment_043_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 40 20 21, g32p_row17_traceSegment_043_0040_0020, g32p_row17_traceSegment_043_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 0 40 41, g32p_row17_traceSegment_043_0000_0040, g32p_row17_traceSegment_043_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 81 10 10, g32p_row17_traceSegment_043_0081_0010, g32p_row17_traceSegment_043_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 101 10 10, g32p_row17_traceSegment_043_0101_0010, g32p_row17_traceSegment_043_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 81 20 20, g32p_row17_traceSegment_043_0081_0020, g32p_row17_traceSegment_043_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 121 10 10, g32p_row17_traceSegment_043_0121_0010, g32p_row17_traceSegment_043_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 141 10 11, g32p_row17_traceSegment_043_0141_0010, g32p_row17_traceSegment_043_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 121 20 21, g32p_row17_traceSegment_043_0121_0020, g32p_row17_traceSegment_043_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 81 40 41, g32p_row17_traceSegment_043_0081_0040, g32p_row17_traceSegment_043_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_043 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 0 81 81, g32p_row17_traceSegment_043_0000_0081, g32p_row17_traceSegment_043_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 162 10 10, g32p_row17_traceSegment_043_0162_0010, g32p_row17_traceSegment_043_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 182 10 10, g32p_row17_traceSegment_043_0182_0010, g32p_row17_traceSegment_043_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 162 20 20, g32p_row17_traceSegment_043_0162_0020, g32p_row17_traceSegment_043_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 202 10 10, g32p_row17_traceSegment_043_0202_0010, g32p_row17_traceSegment_043_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 222 10 11, g32p_row17_traceSegment_043_0222_0010, g32p_row17_traceSegment_043_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 202 20 21, g32p_row17_traceSegment_043_0202_0020, g32p_row17_traceSegment_043_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 162 40 41, g32p_row17_traceSegment_043_0162_0040, g32p_row17_traceSegment_043_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 243 10 10, g32p_row17_traceSegment_043_0243_0010, g32p_row17_traceSegment_043_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 263 10 10, g32p_row17_traceSegment_043_0263_0010, g32p_row17_traceSegment_043_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 243 20 20, g32p_row17_traceSegment_043_0243_0020, g32p_row17_traceSegment_043_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 283 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 283 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 283 10 10, g32p_row17_traceSegment_043_0283_0010, g32p_row17_traceSegment_043_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 303 10 11, g32p_row17_traceSegment_043_0303_0010, g32p_row17_traceSegment_043_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 283 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 283 20 21, g32p_row17_traceSegment_043_0283_0020, g32p_row17_traceSegment_043_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 243 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 243 40 41, g32p_row17_traceSegment_043_0243_0040, g32p_row17_traceSegment_043_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_043 162 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 162 81 81, g32p_row17_traceSegment_043_0162_0081, g32p_row17_traceSegment_043_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_043 0 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 0 162 162, g32p_row17_traceSegment_043_0000_0162, g32p_row17_traceSegment_043_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 324 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 324 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 324 10 10, g32p_row17_traceSegment_043_0324_0010, g32p_row17_traceSegment_043_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 344 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 344 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 344 10 10, g32p_row17_traceSegment_043_0344_0010, g32p_row17_traceSegment_043_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 324 40 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 324 20 20, g32p_row17_traceSegment_043_0324_0020, g32p_row17_traceSegment_043_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 364 10 10, g32p_row17_traceSegment_043_0364_0010, g32p_row17_traceSegment_043_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 384 10 11, g32p_row17_traceSegment_043_0384_0010, g32p_row17_traceSegment_043_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 364 20 21, g32p_row17_traceSegment_043_0364_0020, g32p_row17_traceSegment_043_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 324 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 324 40 41, g32p_row17_traceSegment_043_0324_0040, g32p_row17_traceSegment_043_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 405 10 10, g32p_row17_traceSegment_043_0405_0010, g32p_row17_traceSegment_043_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 425 10 10, g32p_row17_traceSegment_043_0425_0010, g32p_row17_traceSegment_043_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 405 20 20, g32p_row17_traceSegment_043_0405_0020, g32p_row17_traceSegment_043_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 445 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 445 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 445 10 10, g32p_row17_traceSegment_043_0445_0010, g32p_row17_traceSegment_043_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 465 10 11, g32p_row17_traceSegment_043_0465_0010, g32p_row17_traceSegment_043_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 445 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 445 20 21, g32p_row17_traceSegment_043_0445_0020, g32p_row17_traceSegment_043_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 405 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 405 40 41, g32p_row17_traceSegment_043_0405_0040, g32p_row17_traceSegment_043_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_043 324 162 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 324 81 81, g32p_row17_traceSegment_043_0324_0081, g32p_row17_traceSegment_043_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 486 10 10, g32p_row17_traceSegment_043_0486_0010, g32p_row17_traceSegment_043_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 506 10 10, g32p_row17_traceSegment_043_0506_0010, g32p_row17_traceSegment_043_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 486 20 20, g32p_row17_traceSegment_043_0486_0020, g32p_row17_traceSegment_043_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 526 10 10, g32p_row17_traceSegment_043_0526_0010, g32p_row17_traceSegment_043_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 546 10 11, g32p_row17_traceSegment_043_0546_0010, g32p_row17_traceSegment_043_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 526 20 21, g32p_row17_traceSegment_043_0526_0020, g32p_row17_traceSegment_043_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 486 40 41, g32p_row17_traceSegment_043_0486_0040, g32p_row17_traceSegment_043_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 577 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 567 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 567 10 10, g32p_row17_traceSegment_043_0567_0010, g32p_row17_traceSegment_043_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 587 10 10, g32p_row17_traceSegment_043_0587_0010, g32p_row17_traceSegment_043_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 567 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 567 20 20, g32p_row17_traceSegment_043_0567_0020, g32p_row17_traceSegment_043_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 607 10 10, g32p_row17_traceSegment_043_0607_0010, g32p_row17_traceSegment_043_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 627 10 11, g32p_row17_traceSegment_043_0627_0010, g32p_row17_traceSegment_043_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 607 20 21, g32p_row17_traceSegment_043_0607_0020, g32p_row17_traceSegment_043_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 567 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 567 40 41, g32p_row17_traceSegment_043_0567_0040, g32p_row17_traceSegment_043_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_043 486 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 486 81 81, g32p_row17_traceSegment_043_0486_0081, g32p_row17_traceSegment_043_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_043 324 324 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 324 162 162, g32p_row17_traceSegment_043_0324_0162, g32p_row17_traceSegment_043_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_043 0 648 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 0 324 324, g32p_row17_traceSegment_043_0000_0324, g32p_row17_traceSegment_043_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 658 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 648 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 648 10 10, g32p_row17_traceSegment_043_0648_0010, g32p_row17_traceSegment_043_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 668 10 10, g32p_row17_traceSegment_043_0668_0010, g32p_row17_traceSegment_043_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 648 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 648 20 20, g32p_row17_traceSegment_043_0648_0020, g32p_row17_traceSegment_043_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 688 10 10, g32p_row17_traceSegment_043_0688_0010, g32p_row17_traceSegment_043_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 708 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 708 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 708 10 11, g32p_row17_traceSegment_043_0708_0010, g32p_row17_traceSegment_043_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 688 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 688 20 21, g32p_row17_traceSegment_043_0688_0020, g32p_row17_traceSegment_043_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 648 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 648 40 41, g32p_row17_traceSegment_043_0648_0040, g32p_row17_traceSegment_043_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 729 10 10, g32p_row17_traceSegment_043_0729_0010, g32p_row17_traceSegment_043_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 749 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 749 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 749 10 10, g32p_row17_traceSegment_043_0749_0010, g32p_row17_traceSegment_043_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 729 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 729 20 20, g32p_row17_traceSegment_043_0729_0020, g32p_row17_traceSegment_043_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 779 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 769 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 769 10 10, g32p_row17_traceSegment_043_0769_0010, g32p_row17_traceSegment_043_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 789 10 11, g32p_row17_traceSegment_043_0789_0010, g32p_row17_traceSegment_043_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 769 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 769 20 21, g32p_row17_traceSegment_043_0769_0020, g32p_row17_traceSegment_043_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 729 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 729 40 41, g32p_row17_traceSegment_043_0729_0040, g32p_row17_traceSegment_043_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_043 648 162 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 648 81 81, g32p_row17_traceSegment_043_0648_0081, g32p_row17_traceSegment_043_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 810 10 10, g32p_row17_traceSegment_043_0810_0010, g32p_row17_traceSegment_043_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 830 10 10, g32p_row17_traceSegment_043_0830_0010, g32p_row17_traceSegment_043_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 810 20 20, g32p_row17_traceSegment_043_0810_0020, g32p_row17_traceSegment_043_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 850 10 10, g32p_row17_traceSegment_043_0850_0010, g32p_row17_traceSegment_043_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 870 10 11, g32p_row17_traceSegment_043_0870_0010, g32p_row17_traceSegment_043_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 850 20 21, g32p_row17_traceSegment_043_0850_0020, g32p_row17_traceSegment_043_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 810 40 41, g32p_row17_traceSegment_043_0810_0040, g32p_row17_traceSegment_043_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 891 10 10, g32p_row17_traceSegment_043_0891_0010, g32p_row17_traceSegment_043_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 911 10 10, g32p_row17_traceSegment_043_0911_0010, g32p_row17_traceSegment_043_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 891 20 20, g32p_row17_traceSegment_043_0891_0020, g32p_row17_traceSegment_043_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 931 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 931 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 931 10 10, g32p_row17_traceSegment_043_0931_0010, g32p_row17_traceSegment_043_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 951 10 11, g32p_row17_traceSegment_043_0951_0010, g32p_row17_traceSegment_043_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 931 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 931 20 21, g32p_row17_traceSegment_043_0931_0020, g32p_row17_traceSegment_043_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 891 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 891 40 41, g32p_row17_traceSegment_043_0891_0040, g32p_row17_traceSegment_043_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_043 810 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 810 81 81, g32p_row17_traceSegment_043_0810_0081, g32p_row17_traceSegment_043_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_043 648 324 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 648 162 162, g32p_row17_traceSegment_043_0648_0162, g32p_row17_traceSegment_043_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 972 10 10, g32p_row17_traceSegment_043_0972_0010, g32p_row17_traceSegment_043_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 992 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 992 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 992 10 10, g32p_row17_traceSegment_043_0992_0010, g32p_row17_traceSegment_043_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 972 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 972 20 20, g32p_row17_traceSegment_043_0972_0020, g32p_row17_traceSegment_043_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1012 10 10, g32p_row17_traceSegment_043_1012_0010, g32p_row17_traceSegment_043_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1032 10 11, g32p_row17_traceSegment_043_1032_0010, g32p_row17_traceSegment_043_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1012 20 21, g32p_row17_traceSegment_043_1012_0020, g32p_row17_traceSegment_043_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 972 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 972 40 41, g32p_row17_traceSegment_043_0972_0040, g32p_row17_traceSegment_043_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1053 10 10, g32p_row17_traceSegment_043_1053_0010, g32p_row17_traceSegment_043_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1073 10 10, g32p_row17_traceSegment_043_1073_0010, g32p_row17_traceSegment_043_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1053 20 20, g32p_row17_traceSegment_043_1053_0020, g32p_row17_traceSegment_043_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1093 10 10, g32p_row17_traceSegment_043_1093_0010, g32p_row17_traceSegment_043_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1113 10 11, g32p_row17_traceSegment_043_1113_0010, g32p_row17_traceSegment_043_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1093 20 21, g32p_row17_traceSegment_043_1093_0020, g32p_row17_traceSegment_043_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1053 40 41, g32p_row17_traceSegment_043_1053_0040, g32p_row17_traceSegment_043_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_043 972 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 972 81 81, g32p_row17_traceSegment_043_0972_0081, g32p_row17_traceSegment_043_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1134 10 10, g32p_row17_traceSegment_043_1134_0010, g32p_row17_traceSegment_043_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1154 10 10, g32p_row17_traceSegment_043_1154_0010, g32p_row17_traceSegment_043_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1134 20 20, g32p_row17_traceSegment_043_1134_0020, g32p_row17_traceSegment_043_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1174 10 10, g32p_row17_traceSegment_043_1174_0010, g32p_row17_traceSegment_043_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1194 10 11, g32p_row17_traceSegment_043_1194_0010, g32p_row17_traceSegment_043_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1174 20 21, g32p_row17_traceSegment_043_1174_0020, g32p_row17_traceSegment_043_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1134 40 41, g32p_row17_traceSegment_043_1134_0040, g32p_row17_traceSegment_043_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1215 10 10, g32p_row17_traceSegment_043_1215_0010, g32p_row17_traceSegment_043_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1245 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 1235 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1235 10 10, g32p_row17_traceSegment_043_1235_0010, g32p_row17_traceSegment_043_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_043 1215 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1215 20 20, g32p_row17_traceSegment_043_1215_0020, g32p_row17_traceSegment_043_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_043 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1255 10 10, g32p_row17_traceSegment_043_1255_0010, g32p_row17_traceSegment_043_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_043 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_043 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_043_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_043 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1275 10 11, g32p_row17_traceSegment_043_1275_0010, g32p_row17_traceSegment_043_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_043 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1255 20 21, g32p_row17_traceSegment_043_1255_0020, g32p_row17_traceSegment_043_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_043 1215 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1215 40 41, g32p_row17_traceSegment_043_1215_0040, g32p_row17_traceSegment_043_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_043_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_043 1134 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 1134 81 81, g32p_row17_traceSegment_043_1134_0081, g32p_row17_traceSegment_043_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_043 972 324 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 972 162 162, g32p_row17_traceSegment_043_0972_0162, g32p_row17_traceSegment_043_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_043 648 648 = [7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 648 324 324, g32p_row17_traceSegment_043_0648_0324, g32p_row17_traceSegment_043_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_043_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_043 0 1296 = [12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_043 0 648 648, g32p_row17_traceSegment_043_0000_0648, g32p_row17_traceSegment_043_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_043 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 43 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_043_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_044 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 44 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_044_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 0 10 10, g32p_row17_traceSegment_044_0000_0010, g32p_row17_traceSegment_044_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 20 10 10, g32p_row17_traceSegment_044_0020_0010, g32p_row17_traceSegment_044_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 0 20 20, g32p_row17_traceSegment_044_0000_0020, g32p_row17_traceSegment_044_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 40 10 10, g32p_row17_traceSegment_044_0040_0010, g32p_row17_traceSegment_044_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 60 10 11, g32p_row17_traceSegment_044_0060_0010, g32p_row17_traceSegment_044_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 40 20 21, g32p_row17_traceSegment_044_0040_0020, g32p_row17_traceSegment_044_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 0 40 41, g32p_row17_traceSegment_044_0000_0040, g32p_row17_traceSegment_044_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 81 10 10, g32p_row17_traceSegment_044_0081_0010, g32p_row17_traceSegment_044_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 101 10 10, g32p_row17_traceSegment_044_0101_0010, g32p_row17_traceSegment_044_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 81 20 20, g32p_row17_traceSegment_044_0081_0020, g32p_row17_traceSegment_044_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 121 10 10, g32p_row17_traceSegment_044_0121_0010, g32p_row17_traceSegment_044_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 141 10 11, g32p_row17_traceSegment_044_0141_0010, g32p_row17_traceSegment_044_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 121 20 21, g32p_row17_traceSegment_044_0121_0020, g32p_row17_traceSegment_044_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 81 40 41, g32p_row17_traceSegment_044_0081_0040, g32p_row17_traceSegment_044_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_044 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 0 81 81, g32p_row17_traceSegment_044_0000_0081, g32p_row17_traceSegment_044_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 162 10 10, g32p_row17_traceSegment_044_0162_0010, g32p_row17_traceSegment_044_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 182 10 10, g32p_row17_traceSegment_044_0182_0010, g32p_row17_traceSegment_044_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 162 20 20, g32p_row17_traceSegment_044_0162_0020, g32p_row17_traceSegment_044_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 202 10 10, g32p_row17_traceSegment_044_0202_0010, g32p_row17_traceSegment_044_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 222 10 11, g32p_row17_traceSegment_044_0222_0010, g32p_row17_traceSegment_044_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 202 20 21, g32p_row17_traceSegment_044_0202_0020, g32p_row17_traceSegment_044_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 162 40 41, g32p_row17_traceSegment_044_0162_0040, g32p_row17_traceSegment_044_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 243 10 10, g32p_row17_traceSegment_044_0243_0010, g32p_row17_traceSegment_044_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 263 10 10, g32p_row17_traceSegment_044_0263_0010, g32p_row17_traceSegment_044_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 243 20 20, g32p_row17_traceSegment_044_0243_0020, g32p_row17_traceSegment_044_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 283 10 10, g32p_row17_traceSegment_044_0283_0010, g32p_row17_traceSegment_044_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 303 10 11, g32p_row17_traceSegment_044_0303_0010, g32p_row17_traceSegment_044_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 283 20 21, g32p_row17_traceSegment_044_0283_0020, g32p_row17_traceSegment_044_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 243 40 41, g32p_row17_traceSegment_044_0243_0040, g32p_row17_traceSegment_044_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_044 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 162 81 81, g32p_row17_traceSegment_044_0162_0081, g32p_row17_traceSegment_044_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_044 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 0 162 162, g32p_row17_traceSegment_044_0000_0162, g32p_row17_traceSegment_044_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 324 10 10, g32p_row17_traceSegment_044_0324_0010, g32p_row17_traceSegment_044_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 344 10 10, g32p_row17_traceSegment_044_0344_0010, g32p_row17_traceSegment_044_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 324 20 20, g32p_row17_traceSegment_044_0324_0020, g32p_row17_traceSegment_044_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 364 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 364 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 364 10 10, g32p_row17_traceSegment_044_0364_0010, g32p_row17_traceSegment_044_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 384 10 11, g32p_row17_traceSegment_044_0384_0010, g32p_row17_traceSegment_044_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 364 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 364 20 21, g32p_row17_traceSegment_044_0364_0020, g32p_row17_traceSegment_044_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 324 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 324 40 41, g32p_row17_traceSegment_044_0324_0040, g32p_row17_traceSegment_044_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 405 10 10, g32p_row17_traceSegment_044_0405_0010, g32p_row17_traceSegment_044_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 425 10 10, g32p_row17_traceSegment_044_0425_0010, g32p_row17_traceSegment_044_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 405 20 20, g32p_row17_traceSegment_044_0405_0020, g32p_row17_traceSegment_044_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 445 10 10, g32p_row17_traceSegment_044_0445_0010, g32p_row17_traceSegment_044_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 465 10 11, g32p_row17_traceSegment_044_0465_0010, g32p_row17_traceSegment_044_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 445 20 21, g32p_row17_traceSegment_044_0445_0020, g32p_row17_traceSegment_044_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 405 40 41, g32p_row17_traceSegment_044_0405_0040, g32p_row17_traceSegment_044_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_044 324 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 324 81 81, g32p_row17_traceSegment_044_0324_0081, g32p_row17_traceSegment_044_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 486 10 10, g32p_row17_traceSegment_044_0486_0010, g32p_row17_traceSegment_044_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 506 10 10, g32p_row17_traceSegment_044_0506_0010, g32p_row17_traceSegment_044_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 486 20 20, g32p_row17_traceSegment_044_0486_0020, g32p_row17_traceSegment_044_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 526 10 10, g32p_row17_traceSegment_044_0526_0010, g32p_row17_traceSegment_044_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 546 10 11, g32p_row17_traceSegment_044_0546_0010, g32p_row17_traceSegment_044_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 526 20 21, g32p_row17_traceSegment_044_0526_0020, g32p_row17_traceSegment_044_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 486 40 41, g32p_row17_traceSegment_044_0486_0040, g32p_row17_traceSegment_044_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 567 10 10, g32p_row17_traceSegment_044_0567_0010, g32p_row17_traceSegment_044_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 587 10 10, g32p_row17_traceSegment_044_0587_0010, g32p_row17_traceSegment_044_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 567 20 20, g32p_row17_traceSegment_044_0567_0020, g32p_row17_traceSegment_044_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 607 10 10, g32p_row17_traceSegment_044_0607_0010, g32p_row17_traceSegment_044_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 627 10 11, g32p_row17_traceSegment_044_0627_0010, g32p_row17_traceSegment_044_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 607 20 21, g32p_row17_traceSegment_044_0607_0020, g32p_row17_traceSegment_044_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 567 40 41, g32p_row17_traceSegment_044_0567_0040, g32p_row17_traceSegment_044_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_044 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 486 81 81, g32p_row17_traceSegment_044_0486_0081, g32p_row17_traceSegment_044_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_044 324 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 324 162 162, g32p_row17_traceSegment_044_0324_0162, g32p_row17_traceSegment_044_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_044 0 648 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 0 324 324, g32p_row17_traceSegment_044_0000_0324, g32p_row17_traceSegment_044_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 648 10 10, g32p_row17_traceSegment_044_0648_0010, g32p_row17_traceSegment_044_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 668 10 10, g32p_row17_traceSegment_044_0668_0010, g32p_row17_traceSegment_044_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 648 20 20, g32p_row17_traceSegment_044_0648_0020, g32p_row17_traceSegment_044_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 688 10 10, g32p_row17_traceSegment_044_0688_0010, g32p_row17_traceSegment_044_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 708 10 11, g32p_row17_traceSegment_044_0708_0010, g32p_row17_traceSegment_044_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 688 20 21, g32p_row17_traceSegment_044_0688_0020, g32p_row17_traceSegment_044_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 648 40 41, g32p_row17_traceSegment_044_0648_0040, g32p_row17_traceSegment_044_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 729 10 10, g32p_row17_traceSegment_044_0729_0010, g32p_row17_traceSegment_044_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 749 10 10, g32p_row17_traceSegment_044_0749_0010, g32p_row17_traceSegment_044_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 729 20 20, g32p_row17_traceSegment_044_0729_0020, g32p_row17_traceSegment_044_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 769 10 10, g32p_row17_traceSegment_044_0769_0010, g32p_row17_traceSegment_044_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 789 10 11, g32p_row17_traceSegment_044_0789_0010, g32p_row17_traceSegment_044_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 769 20 21, g32p_row17_traceSegment_044_0769_0020, g32p_row17_traceSegment_044_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 729 40 41, g32p_row17_traceSegment_044_0729_0040, g32p_row17_traceSegment_044_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_044 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 648 81 81, g32p_row17_traceSegment_044_0648_0081, g32p_row17_traceSegment_044_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 810 10 10, g32p_row17_traceSegment_044_0810_0010, g32p_row17_traceSegment_044_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 830 10 10, g32p_row17_traceSegment_044_0830_0010, g32p_row17_traceSegment_044_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 810 20 20, g32p_row17_traceSegment_044_0810_0020, g32p_row17_traceSegment_044_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 850 10 10, g32p_row17_traceSegment_044_0850_0010, g32p_row17_traceSegment_044_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 870 10 11, g32p_row17_traceSegment_044_0870_0010, g32p_row17_traceSegment_044_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 850 20 21, g32p_row17_traceSegment_044_0850_0020, g32p_row17_traceSegment_044_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 810 40 41, g32p_row17_traceSegment_044_0810_0040, g32p_row17_traceSegment_044_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 891 10 10, g32p_row17_traceSegment_044_0891_0010, g32p_row17_traceSegment_044_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 911 10 10, g32p_row17_traceSegment_044_0911_0010, g32p_row17_traceSegment_044_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 891 20 20, g32p_row17_traceSegment_044_0891_0020, g32p_row17_traceSegment_044_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 931 10 10, g32p_row17_traceSegment_044_0931_0010, g32p_row17_traceSegment_044_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 951 10 11, g32p_row17_traceSegment_044_0951_0010, g32p_row17_traceSegment_044_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 931 20 21, g32p_row17_traceSegment_044_0931_0020, g32p_row17_traceSegment_044_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 891 40 41, g32p_row17_traceSegment_044_0891_0040, g32p_row17_traceSegment_044_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_044 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 810 81 81, g32p_row17_traceSegment_044_0810_0081, g32p_row17_traceSegment_044_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_044 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 648 162 162, g32p_row17_traceSegment_044_0648_0162, g32p_row17_traceSegment_044_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 972 10 10, g32p_row17_traceSegment_044_0972_0010, g32p_row17_traceSegment_044_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 992 10 10, g32p_row17_traceSegment_044_0992_0010, g32p_row17_traceSegment_044_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 972 20 20, g32p_row17_traceSegment_044_0972_0020, g32p_row17_traceSegment_044_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1012 10 10, g32p_row17_traceSegment_044_1012_0010, g32p_row17_traceSegment_044_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1032 10 11, g32p_row17_traceSegment_044_1032_0010, g32p_row17_traceSegment_044_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1012 20 21, g32p_row17_traceSegment_044_1012_0020, g32p_row17_traceSegment_044_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 972 40 41, g32p_row17_traceSegment_044_0972_0040, g32p_row17_traceSegment_044_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1053 10 10, g32p_row17_traceSegment_044_1053_0010, g32p_row17_traceSegment_044_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1073 10 10, g32p_row17_traceSegment_044_1073_0010, g32p_row17_traceSegment_044_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1053 20 20, g32p_row17_traceSegment_044_1053_0020, g32p_row17_traceSegment_044_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1093 10 10, g32p_row17_traceSegment_044_1093_0010, g32p_row17_traceSegment_044_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1113 10 11, g32p_row17_traceSegment_044_1113_0010, g32p_row17_traceSegment_044_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1093 20 21, g32p_row17_traceSegment_044_1093_0020, g32p_row17_traceSegment_044_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1053 40 41, g32p_row17_traceSegment_044_1053_0040, g32p_row17_traceSegment_044_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_044 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 972 81 81, g32p_row17_traceSegment_044_0972_0081, g32p_row17_traceSegment_044_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1134 10 10, g32p_row17_traceSegment_044_1134_0010, g32p_row17_traceSegment_044_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1154 10 10, g32p_row17_traceSegment_044_1154_0010, g32p_row17_traceSegment_044_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1134 20 20, g32p_row17_traceSegment_044_1134_0020, g32p_row17_traceSegment_044_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1174 10 10, g32p_row17_traceSegment_044_1174_0010, g32p_row17_traceSegment_044_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1194 10 11, g32p_row17_traceSegment_044_1194_0010, g32p_row17_traceSegment_044_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1174 20 21, g32p_row17_traceSegment_044_1174_0020, g32p_row17_traceSegment_044_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1134 40 41, g32p_row17_traceSegment_044_1134_0040, g32p_row17_traceSegment_044_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1215 10 10, g32p_row17_traceSegment_044_1215_0010, g32p_row17_traceSegment_044_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1235 10 10, g32p_row17_traceSegment_044_1235_0010, g32p_row17_traceSegment_044_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_044 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1215 20 20, g32p_row17_traceSegment_044_1215_0020, g32p_row17_traceSegment_044_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_044 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1255 10 10, g32p_row17_traceSegment_044_1255_0010, g32p_row17_traceSegment_044_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_044 1275 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_044 1285 11 = [2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_044_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_044 1275 21 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1275 10 11, g32p_row17_traceSegment_044_1275_0010, g32p_row17_traceSegment_044_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_044 1255 41 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1255 20 21, g32p_row17_traceSegment_044_1255_0020, g32p_row17_traceSegment_044_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_044 1215 81 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1215 40 41, g32p_row17_traceSegment_044_1215_0040, g32p_row17_traceSegment_044_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_044_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_044 1134 162 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 1134 81 81, g32p_row17_traceSegment_044_1134_0081, g32p_row17_traceSegment_044_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_044 972 324 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 972 162 162, g32p_row17_traceSegment_044_0972_0162, g32p_row17_traceSegment_044_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_044 648 648 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 648 324 324, g32p_row17_traceSegment_044_0648_0324, g32p_row17_traceSegment_044_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_044_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_044 0 1296 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_044 0 648 648, g32p_row17_traceSegment_044_0000_0648, g32p_row17_traceSegment_044_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 44 = [4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_044_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_045 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 45 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_045_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 0 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 0 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 0 10 10, g32p_row17_traceSegment_045_0000_0010, g32p_row17_traceSegment_045_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 20 10 10, g32p_row17_traceSegment_045_0020_0010, g32p_row17_traceSegment_045_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 0 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 0 20 20, g32p_row17_traceSegment_045_0000_0020, g32p_row17_traceSegment_045_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 40 10 10, g32p_row17_traceSegment_045_0040_0010, g32p_row17_traceSegment_045_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 60 10 11, g32p_row17_traceSegment_045_0060_0010, g32p_row17_traceSegment_045_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 40 20 21, g32p_row17_traceSegment_045_0040_0020, g32p_row17_traceSegment_045_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 0 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 0 40 41, g32p_row17_traceSegment_045_0000_0040, g32p_row17_traceSegment_045_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 81 10 10, g32p_row17_traceSegment_045_0081_0010, g32p_row17_traceSegment_045_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 101 10 10, g32p_row17_traceSegment_045_0101_0010, g32p_row17_traceSegment_045_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 81 20 20, g32p_row17_traceSegment_045_0081_0020, g32p_row17_traceSegment_045_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 121 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 131 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 121 20 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 121 10 10, g32p_row17_traceSegment_045_0121_0010, g32p_row17_traceSegment_045_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 141 10 11, g32p_row17_traceSegment_045_0141_0010, g32p_row17_traceSegment_045_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 121 41 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 121 20 21, g32p_row17_traceSegment_045_0121_0020, g32p_row17_traceSegment_045_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 81 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 81 40 41, g32p_row17_traceSegment_045_0081_0040, g32p_row17_traceSegment_045_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_045 0 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 0 81 81, g32p_row17_traceSegment_045_0000_0081, g32p_row17_traceSegment_045_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 162 10 10, g32p_row17_traceSegment_045_0162_0010, g32p_row17_traceSegment_045_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 182 10 10, g32p_row17_traceSegment_045_0182_0010, g32p_row17_traceSegment_045_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 162 20 20, g32p_row17_traceSegment_045_0162_0020, g32p_row17_traceSegment_045_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 202 10 10, g32p_row17_traceSegment_045_0202_0010, g32p_row17_traceSegment_045_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 222 10 11, g32p_row17_traceSegment_045_0222_0010, g32p_row17_traceSegment_045_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 202 20 21, g32p_row17_traceSegment_045_0202_0020, g32p_row17_traceSegment_045_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 162 40 41, g32p_row17_traceSegment_045_0162_0040, g32p_row17_traceSegment_045_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 243 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 243 20 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 243 10 10, g32p_row17_traceSegment_045_0243_0010, g32p_row17_traceSegment_045_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 263 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 263 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 263 10 10, g32p_row17_traceSegment_045_0263_0010, g32p_row17_traceSegment_045_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 243 40 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 243 20 20, g32p_row17_traceSegment_045_0243_0020, g32p_row17_traceSegment_045_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 283 10 10, g32p_row17_traceSegment_045_0283_0010, g32p_row17_traceSegment_045_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 303 10 11, g32p_row17_traceSegment_045_0303_0010, g32p_row17_traceSegment_045_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 283 20 21, g32p_row17_traceSegment_045_0283_0020, g32p_row17_traceSegment_045_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 243 81 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 243 40 41, g32p_row17_traceSegment_045_0243_0040, g32p_row17_traceSegment_045_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_045 162 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 162 81 81, g32p_row17_traceSegment_045_0162_0081, g32p_row17_traceSegment_045_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_045 0 324 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 0 162 162, g32p_row17_traceSegment_045_0000_0162, g32p_row17_traceSegment_045_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 324 10 10, g32p_row17_traceSegment_045_0324_0010, g32p_row17_traceSegment_045_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 344 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 344 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 344 10 10, g32p_row17_traceSegment_045_0344_0010, g32p_row17_traceSegment_045_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 324 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 324 20 20, g32p_row17_traceSegment_045_0324_0020, g32p_row17_traceSegment_045_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 364 10 10, g32p_row17_traceSegment_045_0364_0010, g32p_row17_traceSegment_045_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 384 10 11, g32p_row17_traceSegment_045_0384_0010, g32p_row17_traceSegment_045_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 364 20 21, g32p_row17_traceSegment_045_0364_0020, g32p_row17_traceSegment_045_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 324 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 324 40 41, g32p_row17_traceSegment_045_0324_0040, g32p_row17_traceSegment_045_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 415 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 405 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 405 10 10, g32p_row17_traceSegment_045_0405_0010, g32p_row17_traceSegment_045_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 425 10 10, g32p_row17_traceSegment_045_0425_0010, g32p_row17_traceSegment_045_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 405 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 405 20 20, g32p_row17_traceSegment_045_0405_0020, g32p_row17_traceSegment_045_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 445 10 10, g32p_row17_traceSegment_045_0445_0010, g32p_row17_traceSegment_045_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 465 10 11, g32p_row17_traceSegment_045_0465_0010, g32p_row17_traceSegment_045_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 445 20 21, g32p_row17_traceSegment_045_0445_0020, g32p_row17_traceSegment_045_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 405 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 405 40 41, g32p_row17_traceSegment_045_0405_0040, g32p_row17_traceSegment_045_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_045 324 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 324 81 81, g32p_row17_traceSegment_045_0324_0081, g32p_row17_traceSegment_045_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 486 10 10, g32p_row17_traceSegment_045_0486_0010, g32p_row17_traceSegment_045_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 506 10 10, g32p_row17_traceSegment_045_0506_0010, g32p_row17_traceSegment_045_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 486 20 20, g32p_row17_traceSegment_045_0486_0020, g32p_row17_traceSegment_045_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 526 10 10, g32p_row17_traceSegment_045_0526_0010, g32p_row17_traceSegment_045_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 556 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 546 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 546 10 11, g32p_row17_traceSegment_045_0546_0010, g32p_row17_traceSegment_045_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 526 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 526 20 21, g32p_row17_traceSegment_045_0526_0020, g32p_row17_traceSegment_045_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 486 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 486 40 41, g32p_row17_traceSegment_045_0486_0040, g32p_row17_traceSegment_045_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 567 10 10, g32p_row17_traceSegment_045_0567_0010, g32p_row17_traceSegment_045_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 587 10 10, g32p_row17_traceSegment_045_0587_0010, g32p_row17_traceSegment_045_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 567 20 20, g32p_row17_traceSegment_045_0567_0020, g32p_row17_traceSegment_045_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 607 10 10, g32p_row17_traceSegment_045_0607_0010, g32p_row17_traceSegment_045_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 627 10 11, g32p_row17_traceSegment_045_0627_0010, g32p_row17_traceSegment_045_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 607 20 21, g32p_row17_traceSegment_045_0607_0020, g32p_row17_traceSegment_045_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 567 40 41, g32p_row17_traceSegment_045_0567_0040, g32p_row17_traceSegment_045_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_045 486 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 486 81 81, g32p_row17_traceSegment_045_0486_0081, g32p_row17_traceSegment_045_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_045 324 324 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 324 162 162, g32p_row17_traceSegment_045_0324_0162, g32p_row17_traceSegment_045_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_045 0 648 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 0 324 324, g32p_row17_traceSegment_045_0000_0324, g32p_row17_traceSegment_045_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 648 10 10, g32p_row17_traceSegment_045_0648_0010, g32p_row17_traceSegment_045_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 668 10 10, g32p_row17_traceSegment_045_0668_0010, g32p_row17_traceSegment_045_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 648 20 20, g32p_row17_traceSegment_045_0648_0020, g32p_row17_traceSegment_045_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 688 10 10, g32p_row17_traceSegment_045_0688_0010, g32p_row17_traceSegment_045_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 708 10 11, g32p_row17_traceSegment_045_0708_0010, g32p_row17_traceSegment_045_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 688 20 21, g32p_row17_traceSegment_045_0688_0020, g32p_row17_traceSegment_045_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 648 40 41, g32p_row17_traceSegment_045_0648_0040, g32p_row17_traceSegment_045_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 729 10 10, g32p_row17_traceSegment_045_0729_0010, g32p_row17_traceSegment_045_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 749 10 10, g32p_row17_traceSegment_045_0749_0010, g32p_row17_traceSegment_045_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 729 20 20, g32p_row17_traceSegment_045_0729_0020, g32p_row17_traceSegment_045_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 769 10 10, g32p_row17_traceSegment_045_0769_0010, g32p_row17_traceSegment_045_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 789 10 11, g32p_row17_traceSegment_045_0789_0010, g32p_row17_traceSegment_045_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 769 20 21, g32p_row17_traceSegment_045_0769_0020, g32p_row17_traceSegment_045_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 729 40 41, g32p_row17_traceSegment_045_0729_0040, g32p_row17_traceSegment_045_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_045 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 648 81 81, g32p_row17_traceSegment_045_0648_0081, g32p_row17_traceSegment_045_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 810 10 10, g32p_row17_traceSegment_045_0810_0010, g32p_row17_traceSegment_045_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 830 10 10, g32p_row17_traceSegment_045_0830_0010, g32p_row17_traceSegment_045_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 810 20 20, g32p_row17_traceSegment_045_0810_0020, g32p_row17_traceSegment_045_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 850 10 10, g32p_row17_traceSegment_045_0850_0010, g32p_row17_traceSegment_045_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 870 10 11, g32p_row17_traceSegment_045_0870_0010, g32p_row17_traceSegment_045_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 850 20 21, g32p_row17_traceSegment_045_0850_0020, g32p_row17_traceSegment_045_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 810 40 41, g32p_row17_traceSegment_045_0810_0040, g32p_row17_traceSegment_045_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 891 10 10, g32p_row17_traceSegment_045_0891_0010, g32p_row17_traceSegment_045_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 911 10 10, g32p_row17_traceSegment_045_0911_0010, g32p_row17_traceSegment_045_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 891 20 20, g32p_row17_traceSegment_045_0891_0020, g32p_row17_traceSegment_045_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 931 10 10, g32p_row17_traceSegment_045_0931_0010, g32p_row17_traceSegment_045_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 951 10 11, g32p_row17_traceSegment_045_0951_0010, g32p_row17_traceSegment_045_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 931 20 21, g32p_row17_traceSegment_045_0931_0020, g32p_row17_traceSegment_045_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 891 40 41, g32p_row17_traceSegment_045_0891_0040, g32p_row17_traceSegment_045_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_045 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 810 81 81, g32p_row17_traceSegment_045_0810_0081, g32p_row17_traceSegment_045_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_045 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 648 162 162, g32p_row17_traceSegment_045_0648_0162, g32p_row17_traceSegment_045_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 972 10 10, g32p_row17_traceSegment_045_0972_0010, g32p_row17_traceSegment_045_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 992 10 10, g32p_row17_traceSegment_045_0992_0010, g32p_row17_traceSegment_045_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 972 20 20, g32p_row17_traceSegment_045_0972_0020, g32p_row17_traceSegment_045_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1012 10 10, g32p_row17_traceSegment_045_1012_0010, g32p_row17_traceSegment_045_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 1042 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 1032 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1032 10 11, g32p_row17_traceSegment_045_1032_0010, g32p_row17_traceSegment_045_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 1012 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1012 20 21, g32p_row17_traceSegment_045_1012_0020, g32p_row17_traceSegment_045_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 972 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 972 40 41, g32p_row17_traceSegment_045_0972_0040, g32p_row17_traceSegment_045_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1053 10 10, g32p_row17_traceSegment_045_1053_0010, g32p_row17_traceSegment_045_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1073 10 10, g32p_row17_traceSegment_045_1073_0010, g32p_row17_traceSegment_045_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1053 20 20, g32p_row17_traceSegment_045_1053_0020, g32p_row17_traceSegment_045_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1093 10 10, g32p_row17_traceSegment_045_1093_0010, g32p_row17_traceSegment_045_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1113 10 11, g32p_row17_traceSegment_045_1113_0010, g32p_row17_traceSegment_045_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1093 20 21, g32p_row17_traceSegment_045_1093_0020, g32p_row17_traceSegment_045_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1053 40 41, g32p_row17_traceSegment_045_1053_0040, g32p_row17_traceSegment_045_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_045 972 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 972 81 81, g32p_row17_traceSegment_045_0972_0081, g32p_row17_traceSegment_045_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1134 10 10, g32p_row17_traceSegment_045_1134_0010, g32p_row17_traceSegment_045_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1154 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1164 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 1154 20 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1154 10 10, g32p_row17_traceSegment_045_1154_0010, g32p_row17_traceSegment_045_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 1134 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1134 20 20, g32p_row17_traceSegment_045_1134_0020, g32p_row17_traceSegment_045_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1174 10 10, g32p_row17_traceSegment_045_1174_0010, g32p_row17_traceSegment_045_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1194 10 11, g32p_row17_traceSegment_045_1194_0010, g32p_row17_traceSegment_045_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1174 20 21, g32p_row17_traceSegment_045_1174_0020, g32p_row17_traceSegment_045_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 1134 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1134 40 41, g32p_row17_traceSegment_045_1134_0040, g32p_row17_traceSegment_045_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1215 10 10, g32p_row17_traceSegment_045_1215_0010, g32p_row17_traceSegment_045_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1235 10 10, g32p_row17_traceSegment_045_1235_0010, g32p_row17_traceSegment_045_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_045 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1215 20 20, g32p_row17_traceSegment_045_1215_0020, g32p_row17_traceSegment_045_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_045 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1255 10 10, g32p_row17_traceSegment_045_1255_0010, g32p_row17_traceSegment_045_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_045 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_045 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_045_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_045 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1275 10 11, g32p_row17_traceSegment_045_1275_0010, g32p_row17_traceSegment_045_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_045 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1255 20 21, g32p_row17_traceSegment_045_1255_0020, g32p_row17_traceSegment_045_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_045 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1215 40 41, g32p_row17_traceSegment_045_1215_0040, g32p_row17_traceSegment_045_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_045_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_045 1134 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 1134 81 81, g32p_row17_traceSegment_045_1134_0081, g32p_row17_traceSegment_045_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_045 972 324 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 972 162 162, g32p_row17_traceSegment_045_0972_0162, g32p_row17_traceSegment_045_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_045 648 648 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 648 324 324, g32p_row17_traceSegment_045_0648_0324, g32p_row17_traceSegment_045_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_045_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_045 0 1296 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_045 0 648 648, g32p_row17_traceSegment_045_0000_0648, g32p_row17_traceSegment_045_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 45 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_045_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_046 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 46 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_046_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 0 10 10, g32p_row17_traceSegment_046_0000_0010, g32p_row17_traceSegment_046_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 20 10 10, g32p_row17_traceSegment_046_0020_0010, g32p_row17_traceSegment_046_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 0 20 20, g32p_row17_traceSegment_046_0000_0020, g32p_row17_traceSegment_046_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 40 10 10, g32p_row17_traceSegment_046_0040_0010, g32p_row17_traceSegment_046_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 70 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 60 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 60 10 11, g32p_row17_traceSegment_046_0060_0010, g32p_row17_traceSegment_046_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 40 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 40 20 21, g32p_row17_traceSegment_046_0040_0020, g32p_row17_traceSegment_046_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 0 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 0 40 41, g32p_row17_traceSegment_046_0000_0040, g32p_row17_traceSegment_046_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 91 10 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 81 20 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 81 10 10, g32p_row17_traceSegment_046_0081_0010, g32p_row17_traceSegment_046_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 101 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 111 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 101 20 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 101 10 10, g32p_row17_traceSegment_046_0101_0010, g32p_row17_traceSegment_046_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 81 40 = [0, 0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 81 20 20, g32p_row17_traceSegment_046_0081_0020, g32p_row17_traceSegment_046_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 121 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 121 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 121 10 10, g32p_row17_traceSegment_046_0121_0010, g32p_row17_traceSegment_046_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 141 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 151 11 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 141 21 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 141 10 11, g32p_row17_traceSegment_046_0141_0010, g32p_row17_traceSegment_046_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 121 41 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 121 20 21, g32p_row17_traceSegment_046_0121_0020, g32p_row17_traceSegment_046_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 81 81 = [0, 0, 5, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 81 40 41, g32p_row17_traceSegment_046_0081_0040, g32p_row17_traceSegment_046_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_046 0 162 = [0, 0, 6, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 0 81 81, g32p_row17_traceSegment_046_0000_0081, g32p_row17_traceSegment_046_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 162 10 10, g32p_row17_traceSegment_046_0162_0010, g32p_row17_traceSegment_046_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 182 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 192 10 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 182 20 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 182 10 10, g32p_row17_traceSegment_046_0182_0010, g32p_row17_traceSegment_046_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 162 40 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 162 20 20, g32p_row17_traceSegment_046_0162_0020, g32p_row17_traceSegment_046_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 202 10 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 212 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 202 20 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 202 10 10, g32p_row17_traceSegment_046_0202_0010, g32p_row17_traceSegment_046_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 232 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 222 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 222 10 11, g32p_row17_traceSegment_046_0222_0010, g32p_row17_traceSegment_046_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 202 41 = [0, 0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 202 20 21, g32p_row17_traceSegment_046_0202_0020, g32p_row17_traceSegment_046_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 162 81 = [0, 0, 4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 162 40 41, g32p_row17_traceSegment_046_0162_0040, g32p_row17_traceSegment_046_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 253 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 243 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 243 10 10, g32p_row17_traceSegment_046_0243_0010, g32p_row17_traceSegment_046_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 263 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 263 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 263 10 10, g32p_row17_traceSegment_046_0263_0010, g32p_row17_traceSegment_046_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 243 40 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 243 20 20, g32p_row17_traceSegment_046_0243_0020, g32p_row17_traceSegment_046_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 293 10 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 283 20 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 283 10 10, g32p_row17_traceSegment_046_0283_0010, g32p_row17_traceSegment_046_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 303 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 313 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 303 21 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 303 10 11, g32p_row17_traceSegment_046_0303_0010, g32p_row17_traceSegment_046_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 283 41 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 283 20 21, g32p_row17_traceSegment_046_0283_0020, g32p_row17_traceSegment_046_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 243 81 = [0, 0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 243 40 41, g32p_row17_traceSegment_046_0243_0040, g32p_row17_traceSegment_046_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_046 162 162 = [0, 0, 8, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 162 81 81, g32p_row17_traceSegment_046_0162_0081, g32p_row17_traceSegment_046_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_046 0 324 = [0, 0, 14, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 0 162 162, g32p_row17_traceSegment_046_0000_0162, g32p_row17_traceSegment_046_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 334 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 324 20 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 324 10 10, g32p_row17_traceSegment_046_0324_0010, g32p_row17_traceSegment_046_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 344 10 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 354 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 344 20 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 344 10 10, g32p_row17_traceSegment_046_0344_0010, g32p_row17_traceSegment_046_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 324 40 = [0, 0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 324 20 20, g32p_row17_traceSegment_046_0324_0020, g32p_row17_traceSegment_046_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 364 10 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 374 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 364 20 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 364 10 10, g32p_row17_traceSegment_046_0364_0010, g32p_row17_traceSegment_046_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 394 11 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 384 21 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 384 10 11, g32p_row17_traceSegment_046_0384_0010, g32p_row17_traceSegment_046_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 364 41 = [0, 0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 364 20 21, g32p_row17_traceSegment_046_0364_0020, g32p_row17_traceSegment_046_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 324 81 = [0, 0, 5, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 324 40 41, g32p_row17_traceSegment_046_0324_0040, g32p_row17_traceSegment_046_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 405 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 415 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 405 20 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 405 10 10, g32p_row17_traceSegment_046_0405_0010, g32p_row17_traceSegment_046_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 425 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 425 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 425 10 10, g32p_row17_traceSegment_046_0425_0010, g32p_row17_traceSegment_046_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 405 40 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 405 20 20, g32p_row17_traceSegment_046_0405_0020, g32p_row17_traceSegment_046_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 445 10 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 455 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 445 20 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 445 10 10, g32p_row17_traceSegment_046_0445_0010, g32p_row17_traceSegment_046_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 465 10 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 475 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 465 21 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 465 10 11, g32p_row17_traceSegment_046_0465_0010, g32p_row17_traceSegment_046_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 445 41 = [0, 0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 445 20 21, g32p_row17_traceSegment_046_0445_0020, g32p_row17_traceSegment_046_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 405 81 = [0, 0, 4, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 405 40 41, g32p_row17_traceSegment_046_0405_0040, g32p_row17_traceSegment_046_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_046 324 162 = [0, 0, 9, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 324 81 81, g32p_row17_traceSegment_046_0324_0081, g32p_row17_traceSegment_046_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 486 10 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 496 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 486 20 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 486 10 10, g32p_row17_traceSegment_046_0486_0010, g32p_row17_traceSegment_046_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 506 10 = [0, 0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 506 20 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 506 10 10, g32p_row17_traceSegment_046_0506_0010, g32p_row17_traceSegment_046_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 486 40 = [0, 0, 1, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 486 20 20, g32p_row17_traceSegment_046_0486_0020, g32p_row17_traceSegment_046_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 526 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 536 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 526 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 526 10 10, g32p_row17_traceSegment_046_0526_0010, g32p_row17_traceSegment_046_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 546 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 546 21 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 546 10 11, g32p_row17_traceSegment_046_0546_0010, g32p_row17_traceSegment_046_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 526 41 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 526 20 21, g32p_row17_traceSegment_046_0526_0020, g32p_row17_traceSegment_046_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 486 81 = [0, 0, 1, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 486 40 41, g32p_row17_traceSegment_046_0486_0040, g32p_row17_traceSegment_046_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 567 10 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 577 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 567 20 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 567 10 10, g32p_row17_traceSegment_046_0567_0010, g32p_row17_traceSegment_046_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 587 10 10, g32p_row17_traceSegment_046_0587_0010, g32p_row17_traceSegment_046_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 567 40 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 567 20 20, g32p_row17_traceSegment_046_0567_0020, g32p_row17_traceSegment_046_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 607 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 617 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 607 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 607 10 10, g32p_row17_traceSegment_046_0607_0010, g32p_row17_traceSegment_046_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 637 11 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 627 21 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 627 10 11, g32p_row17_traceSegment_046_0627_0010, g32p_row17_traceSegment_046_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 607 41 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 607 20 21, g32p_row17_traceSegment_046_0607_0020, g32p_row17_traceSegment_046_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 567 81 = [0, 0, 1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 567 40 41, g32p_row17_traceSegment_046_0567_0040, g32p_row17_traceSegment_046_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_046 486 162 = [0, 0, 2, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 486 81 81, g32p_row17_traceSegment_046_0486_0081, g32p_row17_traceSegment_046_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_046 324 324 = [0, 0, 11, 0, 0, 27] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 324 162 162, g32p_row17_traceSegment_046_0324_0162, g32p_row17_traceSegment_046_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_046 0 648 = [0, 0, 25, 0, 0, 37] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 0 324 324, g32p_row17_traceSegment_046_0000_0324, g32p_row17_traceSegment_046_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 648 10 10, g32p_row17_traceSegment_046_0648_0010, g32p_row17_traceSegment_046_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 668 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 678 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 668 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 668 10 10, g32p_row17_traceSegment_046_0668_0010, g32p_row17_traceSegment_046_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 648 40 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 648 20 20, g32p_row17_traceSegment_046_0648_0020, g32p_row17_traceSegment_046_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 688 10 10, g32p_row17_traceSegment_046_0688_0010, g32p_row17_traceSegment_046_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 708 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 718 11 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 708 21 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 708 10 11, g32p_row17_traceSegment_046_0708_0010, g32p_row17_traceSegment_046_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 688 41 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 688 20 21, g32p_row17_traceSegment_046_0688_0020, g32p_row17_traceSegment_046_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 648 81 = [0, 0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 648 40 41, g32p_row17_traceSegment_046_0648_0040, g32p_row17_traceSegment_046_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 729 10 10, g32p_row17_traceSegment_046_0729_0010, g32p_row17_traceSegment_046_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 749 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 749 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 749 10 10, g32p_row17_traceSegment_046_0749_0010, g32p_row17_traceSegment_046_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 729 40 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 729 20 20, g32p_row17_traceSegment_046_0729_0020, g32p_row17_traceSegment_046_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 769 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 779 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 769 20 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 769 10 10, g32p_row17_traceSegment_046_0769_0010, g32p_row17_traceSegment_046_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 789 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 789 21 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 789 10 11, g32p_row17_traceSegment_046_0789_0010, g32p_row17_traceSegment_046_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 769 41 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 769 20 21, g32p_row17_traceSegment_046_0769_0020, g32p_row17_traceSegment_046_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 729 81 = [0, 0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 729 40 41, g32p_row17_traceSegment_046_0729_0040, g32p_row17_traceSegment_046_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_046 648 162 = [0, 0, 3, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 648 81 81, g32p_row17_traceSegment_046_0648_0081, g32p_row17_traceSegment_046_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 810 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 820 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 810 20 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 810 10 10, g32p_row17_traceSegment_046_0810_0010, g32p_row17_traceSegment_046_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 840 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 830 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 830 10 10, g32p_row17_traceSegment_046_0830_0010, g32p_row17_traceSegment_046_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 810 40 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 810 20 20, g32p_row17_traceSegment_046_0810_0020, g32p_row17_traceSegment_046_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 860 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 850 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 850 10 10, g32p_row17_traceSegment_046_0850_0010, g32p_row17_traceSegment_046_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 880 11 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 870 21 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 870 10 11, g32p_row17_traceSegment_046_0870_0010, g32p_row17_traceSegment_046_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 850 41 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 850 20 21, g32p_row17_traceSegment_046_0850_0020, g32p_row17_traceSegment_046_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 810 81 = [0, 0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 810 40 41, g32p_row17_traceSegment_046_0810_0040, g32p_row17_traceSegment_046_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 891 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 891 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 891 10 10, g32p_row17_traceSegment_046_0891_0010, g32p_row17_traceSegment_046_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 911 10 10, g32p_row17_traceSegment_046_0911_0010, g32p_row17_traceSegment_046_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 891 40 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 891 20 20, g32p_row17_traceSegment_046_0891_0020, g32p_row17_traceSegment_046_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 931 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 941 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 931 20 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 931 10 10, g32p_row17_traceSegment_046_0931_0010, g32p_row17_traceSegment_046_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 961 11 = [0, 0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 951 21 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 951 10 11, g32p_row17_traceSegment_046_0951_0010, g32p_row17_traceSegment_046_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 931 41 = [0, 0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 931 20 21, g32p_row17_traceSegment_046_0931_0020, g32p_row17_traceSegment_046_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 891 81 = [0, 0, 2, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 891 40 41, g32p_row17_traceSegment_046_0891_0040, g32p_row17_traceSegment_046_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_046 810 162 = [0, 0, 4, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 810 81 81, g32p_row17_traceSegment_046_0810_0081, g32p_row17_traceSegment_046_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_046 648 324 = [0, 0, 7, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 648 162 162, g32p_row17_traceSegment_046_0648_0162, g32p_row17_traceSegment_046_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 972 10 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 982 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 972 20 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 972 10 10, g32p_row17_traceSegment_046_0972_0010, g32p_row17_traceSegment_046_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 992 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1002 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 992 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 992 10 10, g32p_row17_traceSegment_046_0992_0010, g32p_row17_traceSegment_046_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 972 40 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 972 20 20, g32p_row17_traceSegment_046_0972_0020, g32p_row17_traceSegment_046_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1012 10 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1022 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 1012 20 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1012 10 10, g32p_row17_traceSegment_046_1012_0010, g32p_row17_traceSegment_046_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 1042 11 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 1032 21 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1032 10 11, g32p_row17_traceSegment_046_1032_0010, g32p_row17_traceSegment_046_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 1012 41 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1012 20 21, g32p_row17_traceSegment_046_1012_0020, g32p_row17_traceSegment_046_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 972 81 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 972 40 41, g32p_row17_traceSegment_046_0972_0040, g32p_row17_traceSegment_046_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1053 10 10, g32p_row17_traceSegment_046_1053_0010, g32p_row17_traceSegment_046_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1083 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 1073 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1073 10 10, g32p_row17_traceSegment_046_1073_0010, g32p_row17_traceSegment_046_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 1053 40 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1053 20 20, g32p_row17_traceSegment_046_1053_0020, g32p_row17_traceSegment_046_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1093 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1103 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 1093 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1093 10 10, g32p_row17_traceSegment_046_1093_0010, g32p_row17_traceSegment_046_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1113 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 1113 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1113 10 11, g32p_row17_traceSegment_046_1113_0010, g32p_row17_traceSegment_046_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 1093 41 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1093 20 21, g32p_row17_traceSegment_046_1093_0020, g32p_row17_traceSegment_046_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 1053 81 = [0, 0, 1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1053 40 41, g32p_row17_traceSegment_046_1053_0040, g32p_row17_traceSegment_046_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_046 972 162 = [0, 0, 1, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 972 81 81, g32p_row17_traceSegment_046_0972_0081, g32p_row17_traceSegment_046_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1134 10 10, g32p_row17_traceSegment_046_1134_0010, g32p_row17_traceSegment_046_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1154 10 10, g32p_row17_traceSegment_046_1154_0010, g32p_row17_traceSegment_046_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1134 20 20, g32p_row17_traceSegment_046_1134_0020, g32p_row17_traceSegment_046_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1174 10 10, g32p_row17_traceSegment_046_1174_0010, g32p_row17_traceSegment_046_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1194 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 1204 11 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 1194 21 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1194 10 11, g32p_row17_traceSegment_046_1194_0010, g32p_row17_traceSegment_046_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 1174 41 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1174 20 21, g32p_row17_traceSegment_046_1174_0020, g32p_row17_traceSegment_046_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 1134 81 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1134 40 41, g32p_row17_traceSegment_046_1134_0040, g32p_row17_traceSegment_046_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1225 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 1215 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1215 10 10, g32p_row17_traceSegment_046_1215_0010, g32p_row17_traceSegment_046_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1235 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 1235 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1235 10 10, g32p_row17_traceSegment_046_1235_0010, g32p_row17_traceSegment_046_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_046 1215 40 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1215 20 20, g32p_row17_traceSegment_046_1215_0020, g32p_row17_traceSegment_046_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_046 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1255 10 10, g32p_row17_traceSegment_046_1255_0010, g32p_row17_traceSegment_046_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_046 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_046 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_046_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_046 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1275 10 11, g32p_row17_traceSegment_046_1275_0010, g32p_row17_traceSegment_046_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_046 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1255 20 21, g32p_row17_traceSegment_046_1255_0020, g32p_row17_traceSegment_046_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_046 1215 81 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1215 40 41, g32p_row17_traceSegment_046_1215_0040, g32p_row17_traceSegment_046_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_046_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_046 1134 162 = [0, 0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 1134 81 81, g32p_row17_traceSegment_046_1134_0081, g32p_row17_traceSegment_046_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_046 972 324 = [0, 0, 4, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 972 162 162, g32p_row17_traceSegment_046_0972_0162, g32p_row17_traceSegment_046_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_046 648 648 = [0, 0, 11, 0, 0, 35] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 648 324 324, g32p_row17_traceSegment_046_0648_0324, g32p_row17_traceSegment_046_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_046_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_046 0 1296 = [0, 0, 36, 0, 0, 72] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_046 0 648 648, g32p_row17_traceSegment_046_0000_0648, g32p_row17_traceSegment_046_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_046 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 46 = [0, 0, 36, 0, 0, 72] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_046_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_049 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 49 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_049_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 0 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 10 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 0 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 0 10 10, g32p_row17_traceSegment_049_0000_0010, g32p_row17_traceSegment_049_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 20 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 30 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 20 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 20 10 10, g32p_row17_traceSegment_049_0020_0010, g32p_row17_traceSegment_049_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 0 40 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 0 20 20, g32p_row17_traceSegment_049_0000_0020, g32p_row17_traceSegment_049_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 50 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 40 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 40 10 10, g32p_row17_traceSegment_049_0040_0010, g32p_row17_traceSegment_049_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 60 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 70 11 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 60 21 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 60 10 11, g32p_row17_traceSegment_049_0060_0010, g32p_row17_traceSegment_049_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 40 41 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 40 20 21, g32p_row17_traceSegment_049_0040_0020, g32p_row17_traceSegment_049_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 0 81 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 0 40 41, g32p_row17_traceSegment_049_0000_0040, g32p_row17_traceSegment_049_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 81 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 81 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 81 10 10, g32p_row17_traceSegment_049_0081_0010, g32p_row17_traceSegment_049_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 101 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 111 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 101 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 101 10 10, g32p_row17_traceSegment_049_0101_0010, g32p_row17_traceSegment_049_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 81 40 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 81 20 20, g32p_row17_traceSegment_049_0081_0020, g32p_row17_traceSegment_049_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 121 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 131 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 121 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 121 10 10, g32p_row17_traceSegment_049_0121_0010, g32p_row17_traceSegment_049_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 151 11 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 141 21 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 141 10 11, g32p_row17_traceSegment_049_0141_0010, g32p_row17_traceSegment_049_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 121 41 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 121 20 21, g32p_row17_traceSegment_049_0121_0020, g32p_row17_traceSegment_049_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 81 81 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 81 40 41, g32p_row17_traceSegment_049_0081_0040, g32p_row17_traceSegment_049_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_049 0 162 = [0, 0, 0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 0 81 81, g32p_row17_traceSegment_049_0000_0081, g32p_row17_traceSegment_049_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 162 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 172 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 162 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 162 10 10, g32p_row17_traceSegment_049_0162_0010, g32p_row17_traceSegment_049_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 182 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 192 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 182 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 182 10 10, g32p_row17_traceSegment_049_0182_0010, g32p_row17_traceSegment_049_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 162 40 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 162 20 20, g32p_row17_traceSegment_049_0162_0020, g32p_row17_traceSegment_049_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 212 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 202 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 202 10 10, g32p_row17_traceSegment_049_0202_0010, g32p_row17_traceSegment_049_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 222 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 232 11 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 222 21 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 222 10 11, g32p_row17_traceSegment_049_0222_0010, g32p_row17_traceSegment_049_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 202 41 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 202 20 21, g32p_row17_traceSegment_049_0202_0020, g32p_row17_traceSegment_049_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 162 81 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 162 40 41, g32p_row17_traceSegment_049_0162_0040, g32p_row17_traceSegment_049_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 243 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 253 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 243 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 243 10 10, g32p_row17_traceSegment_049_0243_0010, g32p_row17_traceSegment_049_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 263 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 273 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 263 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 263 10 10, g32p_row17_traceSegment_049_0263_0010, g32p_row17_traceSegment_049_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 243 40 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 243 20 20, g32p_row17_traceSegment_049_0243_0020, g32p_row17_traceSegment_049_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 283 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 283 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 283 10 10, g32p_row17_traceSegment_049_0283_0010, g32p_row17_traceSegment_049_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 303 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 313 11 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 303 21 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 303 10 11, g32p_row17_traceSegment_049_0303_0010, g32p_row17_traceSegment_049_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 283 41 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 283 20 21, g32p_row17_traceSegment_049_0283_0020, g32p_row17_traceSegment_049_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 243 81 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 243 40 41, g32p_row17_traceSegment_049_0243_0040, g32p_row17_traceSegment_049_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_049 162 162 = [0, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 162 81 81, g32p_row17_traceSegment_049_0162_0081, g32p_row17_traceSegment_049_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_049 0 324 = [0, 0, 0, 0, 0, 34] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 0 162 162, g32p_row17_traceSegment_049_0000_0162, g32p_row17_traceSegment_049_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 324 10 10, g32p_row17_traceSegment_049_0324_0010, g32p_row17_traceSegment_049_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 344 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 354 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 344 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 344 10 10, g32p_row17_traceSegment_049_0344_0010, g32p_row17_traceSegment_049_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 324 40 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 324 20 20, g32p_row17_traceSegment_049_0324_0020, g32p_row17_traceSegment_049_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 364 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 374 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 364 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 364 10 10, g32p_row17_traceSegment_049_0364_0010, g32p_row17_traceSegment_049_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 384 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 384 21 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 384 10 11, g32p_row17_traceSegment_049_0384_0010, g32p_row17_traceSegment_049_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 364 41 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 364 20 21, g32p_row17_traceSegment_049_0364_0020, g32p_row17_traceSegment_049_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 324 81 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 324 40 41, g32p_row17_traceSegment_049_0324_0040, g32p_row17_traceSegment_049_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 415 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 405 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 405 10 10, g32p_row17_traceSegment_049_0405_0010, g32p_row17_traceSegment_049_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 435 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 425 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 425 10 10, g32p_row17_traceSegment_049_0425_0010, g32p_row17_traceSegment_049_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 405 40 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 405 20 20, g32p_row17_traceSegment_049_0405_0020, g32p_row17_traceSegment_049_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 455 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 445 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 445 10 10, g32p_row17_traceSegment_049_0445_0010, g32p_row17_traceSegment_049_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 465 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 475 11 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 465 21 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 465 10 11, g32p_row17_traceSegment_049_0465_0010, g32p_row17_traceSegment_049_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 445 41 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 445 20 21, g32p_row17_traceSegment_049_0445_0020, g32p_row17_traceSegment_049_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 405 81 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 405 40 41, g32p_row17_traceSegment_049_0405_0040, g32p_row17_traceSegment_049_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_049 324 162 = [0, 0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 324 81 81, g32p_row17_traceSegment_049_0324_0081, g32p_row17_traceSegment_049_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 486 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 496 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 486 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 486 10 10, g32p_row17_traceSegment_049_0486_0010, g32p_row17_traceSegment_049_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 506 10 10, g32p_row17_traceSegment_049_0506_0010, g32p_row17_traceSegment_049_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 486 40 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 486 20 20, g32p_row17_traceSegment_049_0486_0020, g32p_row17_traceSegment_049_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 526 10 10, g32p_row17_traceSegment_049_0526_0010, g32p_row17_traceSegment_049_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 546 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 556 11 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 546 21 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 546 10 11, g32p_row17_traceSegment_049_0546_0010, g32p_row17_traceSegment_049_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 526 41 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 526 20 21, g32p_row17_traceSegment_049_0526_0020, g32p_row17_traceSegment_049_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 486 81 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 486 40 41, g32p_row17_traceSegment_049_0486_0040, g32p_row17_traceSegment_049_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 567 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 567 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 567 10 10, g32p_row17_traceSegment_049_0567_0010, g32p_row17_traceSegment_049_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 587 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 597 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 587 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 587 10 10, g32p_row17_traceSegment_049_0587_0010, g32p_row17_traceSegment_049_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 567 40 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 567 20 20, g32p_row17_traceSegment_049_0567_0020, g32p_row17_traceSegment_049_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 607 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 617 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 607 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 607 10 10, g32p_row17_traceSegment_049_0607_0010, g32p_row17_traceSegment_049_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 627 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 637 11 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 627 21 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 627 10 11, g32p_row17_traceSegment_049_0627_0010, g32p_row17_traceSegment_049_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 607 41 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 607 20 21, g32p_row17_traceSegment_049_0607_0020, g32p_row17_traceSegment_049_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 567 81 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 567 40 41, g32p_row17_traceSegment_049_0567_0040, g32p_row17_traceSegment_049_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_049 486 162 = [0, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 486 81 81, g32p_row17_traceSegment_049_0486_0081, g32p_row17_traceSegment_049_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_049 324 324 = [0, 0, 0, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 324 162 162, g32p_row17_traceSegment_049_0324_0162, g32p_row17_traceSegment_049_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_049 0 648 = [0, 0, 0, 0, 0, 64] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 0 324 324, g32p_row17_traceSegment_049_0000_0324, g32p_row17_traceSegment_049_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 648 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 648 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 648 10 10, g32p_row17_traceSegment_049_0648_0010, g32p_row17_traceSegment_049_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 678 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 668 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 668 10 10, g32p_row17_traceSegment_049_0668_0010, g32p_row17_traceSegment_049_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 648 40 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 648 20 20, g32p_row17_traceSegment_049_0648_0020, g32p_row17_traceSegment_049_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 698 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 688 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 688 10 10, g32p_row17_traceSegment_049_0688_0010, g32p_row17_traceSegment_049_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 718 11 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 708 21 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 708 10 11, g32p_row17_traceSegment_049_0708_0010, g32p_row17_traceSegment_049_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 688 41 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 688 20 21, g32p_row17_traceSegment_049_0688_0020, g32p_row17_traceSegment_049_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 648 81 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 648 40 41, g32p_row17_traceSegment_049_0648_0040, g32p_row17_traceSegment_049_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 729 10 10, g32p_row17_traceSegment_049_0729_0010, g32p_row17_traceSegment_049_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 749 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 749 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 749 10 10, g32p_row17_traceSegment_049_0749_0010, g32p_row17_traceSegment_049_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 729 40 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 729 20 20, g32p_row17_traceSegment_049_0729_0020, g32p_row17_traceSegment_049_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 779 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 769 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 769 10 10, g32p_row17_traceSegment_049_0769_0010, g32p_row17_traceSegment_049_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 789 10 11, g32p_row17_traceSegment_049_0789_0010, g32p_row17_traceSegment_049_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 769 41 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 769 20 21, g32p_row17_traceSegment_049_0769_0020, g32p_row17_traceSegment_049_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 729 81 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 729 40 41, g32p_row17_traceSegment_049_0729_0040, g32p_row17_traceSegment_049_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_049 648 162 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 648 81 81, g32p_row17_traceSegment_049_0648_0081, g32p_row17_traceSegment_049_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 810 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 820 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 810 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 810 10 10, g32p_row17_traceSegment_049_0810_0010, g32p_row17_traceSegment_049_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 830 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 840 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 830 20 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 830 10 10, g32p_row17_traceSegment_049_0830_0010, g32p_row17_traceSegment_049_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 810 40 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 810 20 20, g32p_row17_traceSegment_049_0810_0020, g32p_row17_traceSegment_049_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 850 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 850 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 850 10 10, g32p_row17_traceSegment_049_0850_0010, g32p_row17_traceSegment_049_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 880 11 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 870 21 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 870 10 11, g32p_row17_traceSegment_049_0870_0010, g32p_row17_traceSegment_049_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 850 41 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 850 20 21, g32p_row17_traceSegment_049_0850_0020, g32p_row17_traceSegment_049_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 810 81 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 810 40 41, g32p_row17_traceSegment_049_0810_0040, g32p_row17_traceSegment_049_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 891 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 901 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 891 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 891 10 10, g32p_row17_traceSegment_049_0891_0010, g32p_row17_traceSegment_049_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 911 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 921 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 911 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 911 10 10, g32p_row17_traceSegment_049_0911_0010, g32p_row17_traceSegment_049_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 891 40 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 891 20 20, g32p_row17_traceSegment_049_0891_0020, g32p_row17_traceSegment_049_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 941 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 931 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 931 10 10, g32p_row17_traceSegment_049_0931_0010, g32p_row17_traceSegment_049_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 951 10 11, g32p_row17_traceSegment_049_0951_0010, g32p_row17_traceSegment_049_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 931 41 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 931 20 21, g32p_row17_traceSegment_049_0931_0020, g32p_row17_traceSegment_049_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 891 81 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 891 40 41, g32p_row17_traceSegment_049_0891_0040, g32p_row17_traceSegment_049_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_049 810 162 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 810 81 81, g32p_row17_traceSegment_049_0810_0081, g32p_row17_traceSegment_049_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_049 648 324 = [0, 0, 0, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 648 162 162, g32p_row17_traceSegment_049_0648_0162, g32p_row17_traceSegment_049_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 972 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 982 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 972 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 972 10 10, g32p_row17_traceSegment_049_0972_0010, g32p_row17_traceSegment_049_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 992 10 10, g32p_row17_traceSegment_049_0992_0010, g32p_row17_traceSegment_049_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 972 40 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 972 20 20, g32p_row17_traceSegment_049_0972_0020, g32p_row17_traceSegment_049_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1022 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 1012 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1012 10 10, g32p_row17_traceSegment_049_1012_0010, g32p_row17_traceSegment_049_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1032 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 1042 11 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 1032 21 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1032 10 11, g32p_row17_traceSegment_049_1032_0010, g32p_row17_traceSegment_049_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 1012 41 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1012 20 21, g32p_row17_traceSegment_049_1012_0020, g32p_row17_traceSegment_049_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 972 81 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 972 40 41, g32p_row17_traceSegment_049_0972_0040, g32p_row17_traceSegment_049_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1053 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1063 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 1053 20 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1053 10 10, g32p_row17_traceSegment_049_1053_0010, g32p_row17_traceSegment_049_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1073 10 10, g32p_row17_traceSegment_049_1073_0010, g32p_row17_traceSegment_049_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 1053 40 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1053 20 20, g32p_row17_traceSegment_049_1053_0020, g32p_row17_traceSegment_049_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1103 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 1093 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1093 10 10, g32p_row17_traceSegment_049_1093_0010, g32p_row17_traceSegment_049_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1113 10 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 1123 11 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 1113 21 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1113 10 11, g32p_row17_traceSegment_049_1113_0010, g32p_row17_traceSegment_049_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 1093 41 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1093 20 21, g32p_row17_traceSegment_049_1093_0020, g32p_row17_traceSegment_049_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 1053 81 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1053 40 41, g32p_row17_traceSegment_049_1053_0040, g32p_row17_traceSegment_049_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_049 972 162 = [0, 0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 972 81 81, g32p_row17_traceSegment_049_0972_0081, g32p_row17_traceSegment_049_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1144 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 1134 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1134 10 10, g32p_row17_traceSegment_049_1134_0010, g32p_row17_traceSegment_049_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1154 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 1154 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1154 10 10, g32p_row17_traceSegment_049_1154_0010, g32p_row17_traceSegment_049_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 1134 40 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1134 20 20, g32p_row17_traceSegment_049_1134_0020, g32p_row17_traceSegment_049_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1174 10 10, g32p_row17_traceSegment_049_1174_0010, g32p_row17_traceSegment_049_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1194 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 1194 21 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1194 10 11, g32p_row17_traceSegment_049_1194_0010, g32p_row17_traceSegment_049_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 1174 41 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1174 20 21, g32p_row17_traceSegment_049_1174_0020, g32p_row17_traceSegment_049_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 1134 81 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1134 40 41, g32p_row17_traceSegment_049_1134_0040, g32p_row17_traceSegment_049_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1215 10 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1225 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 1215 20 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1215 10 10, g32p_row17_traceSegment_049_1215_0010, g32p_row17_traceSegment_049_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1245 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 1235 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1235 10 10, g32p_row17_traceSegment_049_1235_0010, g32p_row17_traceSegment_049_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_049 1215 40 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1215 20 20, g32p_row17_traceSegment_049_1215_0020, g32p_row17_traceSegment_049_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1265 10 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_049 1255 20 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1255 10 10, g32p_row17_traceSegment_049_1255_0010, g32p_row17_traceSegment_049_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_049 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_049 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_049_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_049 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1275 10 11, g32p_row17_traceSegment_049_1275_0010, g32p_row17_traceSegment_049_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_049 1255 41 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1255 20 21, g32p_row17_traceSegment_049_1255_0020, g32p_row17_traceSegment_049_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_049 1215 81 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1215 40 41, g32p_row17_traceSegment_049_1215_0040, g32p_row17_traceSegment_049_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_049_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_049 1134 162 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 1134 81 81, g32p_row17_traceSegment_049_1134_0081, g32p_row17_traceSegment_049_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_049 972 324 = [0, 0, 0, 0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 972 162 162, g32p_row17_traceSegment_049_0972_0162, g32p_row17_traceSegment_049_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_049 648 648 = [0, 0, 0, 0, 0, 44] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 648 324 324, g32p_row17_traceSegment_049_0648_0324, g32p_row17_traceSegment_049_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_049_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_049 0 1296 = [0, 0, 0, 0, 0, 108] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_049 0 648 648, g32p_row17_traceSegment_049_0000_0648, g32p_row17_traceSegment_049_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_049 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 49 = [0, 0, 0, 0, 0, 108] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_049_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_050 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 50 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_050_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 0 10 10, g32p_row17_traceSegment_050_0000_0010, g32p_row17_traceSegment_050_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 20 10 10, g32p_row17_traceSegment_050_0020_0010, g32p_row17_traceSegment_050_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 0 20 20, g32p_row17_traceSegment_050_0000_0020, g32p_row17_traceSegment_050_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 40 10 10, g32p_row17_traceSegment_050_0040_0010, g32p_row17_traceSegment_050_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 60 10 11, g32p_row17_traceSegment_050_0060_0010, g32p_row17_traceSegment_050_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 40 20 21, g32p_row17_traceSegment_050_0040_0020, g32p_row17_traceSegment_050_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 0 40 41, g32p_row17_traceSegment_050_0000_0040, g32p_row17_traceSegment_050_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 81 10 10, g32p_row17_traceSegment_050_0081_0010, g32p_row17_traceSegment_050_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 101 10 10, g32p_row17_traceSegment_050_0101_0010, g32p_row17_traceSegment_050_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 81 20 20, g32p_row17_traceSegment_050_0081_0020, g32p_row17_traceSegment_050_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 121 10 10, g32p_row17_traceSegment_050_0121_0010, g32p_row17_traceSegment_050_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 141 10 11, g32p_row17_traceSegment_050_0141_0010, g32p_row17_traceSegment_050_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 121 20 21, g32p_row17_traceSegment_050_0121_0020, g32p_row17_traceSegment_050_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 81 40 41, g32p_row17_traceSegment_050_0081_0040, g32p_row17_traceSegment_050_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_050 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 0 81 81, g32p_row17_traceSegment_050_0000_0081, g32p_row17_traceSegment_050_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 162 10 10, g32p_row17_traceSegment_050_0162_0010, g32p_row17_traceSegment_050_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 182 10 10, g32p_row17_traceSegment_050_0182_0010, g32p_row17_traceSegment_050_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 162 20 20, g32p_row17_traceSegment_050_0162_0020, g32p_row17_traceSegment_050_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 202 10 10, g32p_row17_traceSegment_050_0202_0010, g32p_row17_traceSegment_050_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 222 10 11, g32p_row17_traceSegment_050_0222_0010, g32p_row17_traceSegment_050_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 202 20 21, g32p_row17_traceSegment_050_0202_0020, g32p_row17_traceSegment_050_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 162 40 41, g32p_row17_traceSegment_050_0162_0040, g32p_row17_traceSegment_050_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 243 10 10, g32p_row17_traceSegment_050_0243_0010, g32p_row17_traceSegment_050_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 263 10 10, g32p_row17_traceSegment_050_0263_0010, g32p_row17_traceSegment_050_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 243 20 20, g32p_row17_traceSegment_050_0243_0020, g32p_row17_traceSegment_050_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 283 10 10, g32p_row17_traceSegment_050_0283_0010, g32p_row17_traceSegment_050_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 303 10 11, g32p_row17_traceSegment_050_0303_0010, g32p_row17_traceSegment_050_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 283 20 21, g32p_row17_traceSegment_050_0283_0020, g32p_row17_traceSegment_050_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 243 40 41, g32p_row17_traceSegment_050_0243_0040, g32p_row17_traceSegment_050_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_050 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 162 81 81, g32p_row17_traceSegment_050_0162_0081, g32p_row17_traceSegment_050_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_050 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 0 162 162, g32p_row17_traceSegment_050_0000_0162, g32p_row17_traceSegment_050_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 324 10 10, g32p_row17_traceSegment_050_0324_0010, g32p_row17_traceSegment_050_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 344 10 10, g32p_row17_traceSegment_050_0344_0010, g32p_row17_traceSegment_050_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 324 20 20, g32p_row17_traceSegment_050_0324_0020, g32p_row17_traceSegment_050_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 364 10 10, g32p_row17_traceSegment_050_0364_0010, g32p_row17_traceSegment_050_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 384 10 11, g32p_row17_traceSegment_050_0384_0010, g32p_row17_traceSegment_050_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 364 20 21, g32p_row17_traceSegment_050_0364_0020, g32p_row17_traceSegment_050_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 324 40 41, g32p_row17_traceSegment_050_0324_0040, g32p_row17_traceSegment_050_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 405 10 10, g32p_row17_traceSegment_050_0405_0010, g32p_row17_traceSegment_050_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 425 10 10, g32p_row17_traceSegment_050_0425_0010, g32p_row17_traceSegment_050_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 405 20 20, g32p_row17_traceSegment_050_0405_0020, g32p_row17_traceSegment_050_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 445 10 10, g32p_row17_traceSegment_050_0445_0010, g32p_row17_traceSegment_050_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 465 10 11, g32p_row17_traceSegment_050_0465_0010, g32p_row17_traceSegment_050_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 445 20 21, g32p_row17_traceSegment_050_0445_0020, g32p_row17_traceSegment_050_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 405 40 41, g32p_row17_traceSegment_050_0405_0040, g32p_row17_traceSegment_050_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_050 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 324 81 81, g32p_row17_traceSegment_050_0324_0081, g32p_row17_traceSegment_050_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 486 10 10, g32p_row17_traceSegment_050_0486_0010, g32p_row17_traceSegment_050_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 506 10 10, g32p_row17_traceSegment_050_0506_0010, g32p_row17_traceSegment_050_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 486 20 20, g32p_row17_traceSegment_050_0486_0020, g32p_row17_traceSegment_050_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 526 10 10, g32p_row17_traceSegment_050_0526_0010, g32p_row17_traceSegment_050_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 546 10 11, g32p_row17_traceSegment_050_0546_0010, g32p_row17_traceSegment_050_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 526 20 21, g32p_row17_traceSegment_050_0526_0020, g32p_row17_traceSegment_050_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 486 40 41, g32p_row17_traceSegment_050_0486_0040, g32p_row17_traceSegment_050_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 567 10 10, g32p_row17_traceSegment_050_0567_0010, g32p_row17_traceSegment_050_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 587 10 10, g32p_row17_traceSegment_050_0587_0010, g32p_row17_traceSegment_050_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 567 20 20, g32p_row17_traceSegment_050_0567_0020, g32p_row17_traceSegment_050_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 607 10 10, g32p_row17_traceSegment_050_0607_0010, g32p_row17_traceSegment_050_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 627 10 11, g32p_row17_traceSegment_050_0627_0010, g32p_row17_traceSegment_050_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 607 20 21, g32p_row17_traceSegment_050_0607_0020, g32p_row17_traceSegment_050_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 567 40 41, g32p_row17_traceSegment_050_0567_0040, g32p_row17_traceSegment_050_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_050 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 486 81 81, g32p_row17_traceSegment_050_0486_0081, g32p_row17_traceSegment_050_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_050 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 324 162 162, g32p_row17_traceSegment_050_0324_0162, g32p_row17_traceSegment_050_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_050 0 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 0 324 324, g32p_row17_traceSegment_050_0000_0324, g32p_row17_traceSegment_050_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 648 10 10, g32p_row17_traceSegment_050_0648_0010, g32p_row17_traceSegment_050_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 678 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 668 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 668 10 10, g32p_row17_traceSegment_050_0668_0010, g32p_row17_traceSegment_050_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 648 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 648 20 20, g32p_row17_traceSegment_050_0648_0020, g32p_row17_traceSegment_050_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 688 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 688 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 688 10 10, g32p_row17_traceSegment_050_0688_0010, g32p_row17_traceSegment_050_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 708 10 11, g32p_row17_traceSegment_050_0708_0010, g32p_row17_traceSegment_050_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 688 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 688 20 21, g32p_row17_traceSegment_050_0688_0020, g32p_row17_traceSegment_050_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 648 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 648 40 41, g32p_row17_traceSegment_050_0648_0040, g32p_row17_traceSegment_050_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 729 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 729 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 729 10 10, g32p_row17_traceSegment_050_0729_0010, g32p_row17_traceSegment_050_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 759 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 749 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 749 10 10, g32p_row17_traceSegment_050_0749_0010, g32p_row17_traceSegment_050_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 729 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 729 20 20, g32p_row17_traceSegment_050_0729_0020, g32p_row17_traceSegment_050_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 769 10 10, g32p_row17_traceSegment_050_0769_0010, g32p_row17_traceSegment_050_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 789 10 11, g32p_row17_traceSegment_050_0789_0010, g32p_row17_traceSegment_050_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 769 20 21, g32p_row17_traceSegment_050_0769_0020, g32p_row17_traceSegment_050_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 729 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 729 40 41, g32p_row17_traceSegment_050_0729_0040, g32p_row17_traceSegment_050_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_050 648 162 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 648 81 81, g32p_row17_traceSegment_050_0648_0081, g32p_row17_traceSegment_050_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 810 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 810 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 810 10 10, g32p_row17_traceSegment_050_0810_0010, g32p_row17_traceSegment_050_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 830 10 10, g32p_row17_traceSegment_050_0830_0010, g32p_row17_traceSegment_050_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 810 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 810 20 20, g32p_row17_traceSegment_050_0810_0020, g32p_row17_traceSegment_050_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 850 10 10, g32p_row17_traceSegment_050_0850_0010, g32p_row17_traceSegment_050_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 870 10 11, g32p_row17_traceSegment_050_0870_0010, g32p_row17_traceSegment_050_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 850 20 21, g32p_row17_traceSegment_050_0850_0020, g32p_row17_traceSegment_050_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 810 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 810 40 41, g32p_row17_traceSegment_050_0810_0040, g32p_row17_traceSegment_050_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 891 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 891 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 891 10 10, g32p_row17_traceSegment_050_0891_0010, g32p_row17_traceSegment_050_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 911 10 10, g32p_row17_traceSegment_050_0911_0010, g32p_row17_traceSegment_050_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 891 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 891 20 20, g32p_row17_traceSegment_050_0891_0020, g32p_row17_traceSegment_050_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 931 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 931 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 931 10 10, g32p_row17_traceSegment_050_0931_0010, g32p_row17_traceSegment_050_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 951 10 11, g32p_row17_traceSegment_050_0951_0010, g32p_row17_traceSegment_050_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 931 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 931 20 21, g32p_row17_traceSegment_050_0931_0020, g32p_row17_traceSegment_050_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 891 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 891 40 41, g32p_row17_traceSegment_050_0891_0040, g32p_row17_traceSegment_050_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_050 810 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 810 81 81, g32p_row17_traceSegment_050_0810_0081, g32p_row17_traceSegment_050_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_050 648 324 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 648 162 162, g32p_row17_traceSegment_050_0648_0162, g32p_row17_traceSegment_050_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 972 10 10, g32p_row17_traceSegment_050_0972_0010, g32p_row17_traceSegment_050_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 992 10 10, g32p_row17_traceSegment_050_0992_0010, g32p_row17_traceSegment_050_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 972 20 20, g32p_row17_traceSegment_050_0972_0020, g32p_row17_traceSegment_050_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1012 10 10, g32p_row17_traceSegment_050_1012_0010, g32p_row17_traceSegment_050_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1032 10 11, g32p_row17_traceSegment_050_1032_0010, g32p_row17_traceSegment_050_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1012 20 21, g32p_row17_traceSegment_050_1012_0020, g32p_row17_traceSegment_050_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 972 40 41, g32p_row17_traceSegment_050_0972_0040, g32p_row17_traceSegment_050_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1053 10 10, g32p_row17_traceSegment_050_1053_0010, g32p_row17_traceSegment_050_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1073 10 10, g32p_row17_traceSegment_050_1073_0010, g32p_row17_traceSegment_050_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1053 20 20, g32p_row17_traceSegment_050_1053_0020, g32p_row17_traceSegment_050_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1093 10 10, g32p_row17_traceSegment_050_1093_0010, g32p_row17_traceSegment_050_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 1123 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 1113 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1113 10 11, g32p_row17_traceSegment_050_1113_0010, g32p_row17_traceSegment_050_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 1093 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1093 20 21, g32p_row17_traceSegment_050_1093_0020, g32p_row17_traceSegment_050_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 1053 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1053 40 41, g32p_row17_traceSegment_050_1053_0040, g32p_row17_traceSegment_050_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_050 972 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 972 81 81, g32p_row17_traceSegment_050_0972_0081, g32p_row17_traceSegment_050_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1134 10 10, g32p_row17_traceSegment_050_1134_0010, g32p_row17_traceSegment_050_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1154 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 1154 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1154 10 10, g32p_row17_traceSegment_050_1154_0010, g32p_row17_traceSegment_050_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 1134 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1134 20 20, g32p_row17_traceSegment_050_1134_0020, g32p_row17_traceSegment_050_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1174 10 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 1174 20 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1174 10 10, g32p_row17_traceSegment_050_1174_0010, g32p_row17_traceSegment_050_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 1204 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 1194 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1194 10 11, g32p_row17_traceSegment_050_1194_0010, g32p_row17_traceSegment_050_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 1174 41 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1174 20 21, g32p_row17_traceSegment_050_1174_0020, g32p_row17_traceSegment_050_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 1134 81 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1134 40 41, g32p_row17_traceSegment_050_1134_0040, g32p_row17_traceSegment_050_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1215 10 10, g32p_row17_traceSegment_050_1215_0010, g32p_row17_traceSegment_050_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1235 10 10, g32p_row17_traceSegment_050_1235_0010, g32p_row17_traceSegment_050_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_050 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1215 20 20, g32p_row17_traceSegment_050_1215_0020, g32p_row17_traceSegment_050_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_050 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1255 10 10, g32p_row17_traceSegment_050_1255_0010, g32p_row17_traceSegment_050_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_050 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_050 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_050_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_050 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1275 10 11, g32p_row17_traceSegment_050_1275_0010, g32p_row17_traceSegment_050_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_050 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1255 20 21, g32p_row17_traceSegment_050_1255_0020, g32p_row17_traceSegment_050_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_050 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1215 40 41, g32p_row17_traceSegment_050_1215_0040, g32p_row17_traceSegment_050_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_050_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_050 1134 162 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 1134 81 81, g32p_row17_traceSegment_050_1134_0081, g32p_row17_traceSegment_050_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_050 972 324 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 972 162 162, g32p_row17_traceSegment_050_0972_0162, g32p_row17_traceSegment_050_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_050 648 648 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 648 324 324, g32p_row17_traceSegment_050_0648_0324, g32p_row17_traceSegment_050_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_050_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_050 0 1296 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_050 0 648 648, g32p_row17_traceSegment_050_0000_0648, g32p_row17_traceSegment_050_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_050 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 50 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_050_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_tracePolynomial_038 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 38) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 38) (g32p_literalTraceValue 16 38)
      [1, -1, 1] [2592, 2592] = true := by
  rw [g32p_row17_traceCoefficients_038]
  decide +kernel

theorem g32p_row17_tracePolynomial_040 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 40) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 40) (g32p_literalTraceValue 16 40)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_040]
  decide +kernel

theorem g32p_row17_tracePolynomial_043 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 43) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 43) (g32p_literalTraceValue 16 43)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_043]
  decide +kernel

theorem g32p_row17_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 44) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 44) (g32p_literalTraceValue 16 44)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_044]
  decide +kernel

theorem g32p_row17_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 45) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 45) (g32p_literalTraceValue 16 45)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_045]
  decide +kernel

theorem g32p_row17_tracePolynomial_046 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 46) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 46) (g32p_literalTraceValue 16 46)
      [1, -1, 1] [0, 0, 2592, 2592] = true := by
  rw [g32p_row17_traceCoefficients_046]
  decide +kernel

theorem g32p_row17_tracePolynomial_049 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 49) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 49) (g32p_literalTraceValue 16 49)
      [1, -1, 1] [0, 0, 2592, 2592] = true := by
  rw [g32p_row17_traceCoefficients_049]
  decide +kernel

theorem g32p_row17_tracePolynomial_050 :
    g32p_supplierTracePolynomialCheck 1296 (g32p_literalCentralizer 50) 6
      (g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 50) (g32p_literalTraceValue 16 50)
      [1, -1, 1] [] = true := by
  rw [g32p_row17_traceCoefficients_050]
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

private def g32p_row17_traceSegment_051 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 51 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_051_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 0 10 10, g32p_row17_traceSegment_051_0000_0010, g32p_row17_traceSegment_051_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 20 10 10, g32p_row17_traceSegment_051_0020_0010, g32p_row17_traceSegment_051_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 0 20 20, g32p_row17_traceSegment_051_0000_0020, g32p_row17_traceSegment_051_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 40 10 10, g32p_row17_traceSegment_051_0040_0010, g32p_row17_traceSegment_051_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 60 10 11, g32p_row17_traceSegment_051_0060_0010, g32p_row17_traceSegment_051_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 40 20 21, g32p_row17_traceSegment_051_0040_0020, g32p_row17_traceSegment_051_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 0 40 41, g32p_row17_traceSegment_051_0000_0040, g32p_row17_traceSegment_051_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 81 10 10, g32p_row17_traceSegment_051_0081_0010, g32p_row17_traceSegment_051_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 101 10 10, g32p_row17_traceSegment_051_0101_0010, g32p_row17_traceSegment_051_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 81 20 20, g32p_row17_traceSegment_051_0081_0020, g32p_row17_traceSegment_051_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 121 10 10, g32p_row17_traceSegment_051_0121_0010, g32p_row17_traceSegment_051_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 141 10 11, g32p_row17_traceSegment_051_0141_0010, g32p_row17_traceSegment_051_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 121 20 21, g32p_row17_traceSegment_051_0121_0020, g32p_row17_traceSegment_051_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 81 40 41, g32p_row17_traceSegment_051_0081_0040, g32p_row17_traceSegment_051_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_051 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 0 81 81, g32p_row17_traceSegment_051_0000_0081, g32p_row17_traceSegment_051_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 162 10 10, g32p_row17_traceSegment_051_0162_0010, g32p_row17_traceSegment_051_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 182 10 10, g32p_row17_traceSegment_051_0182_0010, g32p_row17_traceSegment_051_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 162 20 20, g32p_row17_traceSegment_051_0162_0020, g32p_row17_traceSegment_051_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 202 10 10, g32p_row17_traceSegment_051_0202_0010, g32p_row17_traceSegment_051_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 222 10 11, g32p_row17_traceSegment_051_0222_0010, g32p_row17_traceSegment_051_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 202 20 21, g32p_row17_traceSegment_051_0202_0020, g32p_row17_traceSegment_051_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 162 40 41, g32p_row17_traceSegment_051_0162_0040, g32p_row17_traceSegment_051_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 243 10 10, g32p_row17_traceSegment_051_0243_0010, g32p_row17_traceSegment_051_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 263 10 10, g32p_row17_traceSegment_051_0263_0010, g32p_row17_traceSegment_051_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 243 20 20, g32p_row17_traceSegment_051_0243_0020, g32p_row17_traceSegment_051_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 283 10 10, g32p_row17_traceSegment_051_0283_0010, g32p_row17_traceSegment_051_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 303 10 11, g32p_row17_traceSegment_051_0303_0010, g32p_row17_traceSegment_051_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 283 20 21, g32p_row17_traceSegment_051_0283_0020, g32p_row17_traceSegment_051_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 243 40 41, g32p_row17_traceSegment_051_0243_0040, g32p_row17_traceSegment_051_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_051 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 162 81 81, g32p_row17_traceSegment_051_0162_0081, g32p_row17_traceSegment_051_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_051 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 0 162 162, g32p_row17_traceSegment_051_0000_0162, g32p_row17_traceSegment_051_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 324 10 10, g32p_row17_traceSegment_051_0324_0010, g32p_row17_traceSegment_051_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 344 10 10, g32p_row17_traceSegment_051_0344_0010, g32p_row17_traceSegment_051_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 324 20 20, g32p_row17_traceSegment_051_0324_0020, g32p_row17_traceSegment_051_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 364 10 10, g32p_row17_traceSegment_051_0364_0010, g32p_row17_traceSegment_051_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 384 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 384 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 384 10 11, g32p_row17_traceSegment_051_0384_0010, g32p_row17_traceSegment_051_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 364 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 364 20 21, g32p_row17_traceSegment_051_0364_0020, g32p_row17_traceSegment_051_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 324 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 324 40 41, g32p_row17_traceSegment_051_0324_0040, g32p_row17_traceSegment_051_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 405 10 10, g32p_row17_traceSegment_051_0405_0010, g32p_row17_traceSegment_051_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 425 10 10, g32p_row17_traceSegment_051_0425_0010, g32p_row17_traceSegment_051_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 405 20 20, g32p_row17_traceSegment_051_0405_0020, g32p_row17_traceSegment_051_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 455 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 445 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 445 10 10, g32p_row17_traceSegment_051_0445_0010, g32p_row17_traceSegment_051_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 475 11 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 465 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 465 10 11, g32p_row17_traceSegment_051_0465_0010, g32p_row17_traceSegment_051_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 445 41 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 445 20 21, g32p_row17_traceSegment_051_0445_0020, g32p_row17_traceSegment_051_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 405 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 405 40 41, g32p_row17_traceSegment_051_0405_0040, g32p_row17_traceSegment_051_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_051 324 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 324 81 81, g32p_row17_traceSegment_051_0324_0081, g32p_row17_traceSegment_051_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 486 10 10, g32p_row17_traceSegment_051_0486_0010, g32p_row17_traceSegment_051_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 506 10 10, g32p_row17_traceSegment_051_0506_0010, g32p_row17_traceSegment_051_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 486 20 20, g32p_row17_traceSegment_051_0486_0020, g32p_row17_traceSegment_051_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 526 10 10, g32p_row17_traceSegment_051_0526_0010, g32p_row17_traceSegment_051_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 546 10 11, g32p_row17_traceSegment_051_0546_0010, g32p_row17_traceSegment_051_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 526 20 21, g32p_row17_traceSegment_051_0526_0020, g32p_row17_traceSegment_051_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 486 40 41, g32p_row17_traceSegment_051_0486_0040, g32p_row17_traceSegment_051_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 567 10 10, g32p_row17_traceSegment_051_0567_0010, g32p_row17_traceSegment_051_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 597 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 587 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 587 10 10, g32p_row17_traceSegment_051_0587_0010, g32p_row17_traceSegment_051_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 567 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 567 20 20, g32p_row17_traceSegment_051_0567_0020, g32p_row17_traceSegment_051_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 607 10 10, g32p_row17_traceSegment_051_0607_0010, g32p_row17_traceSegment_051_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 627 10 11, g32p_row17_traceSegment_051_0627_0010, g32p_row17_traceSegment_051_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 607 20 21, g32p_row17_traceSegment_051_0607_0020, g32p_row17_traceSegment_051_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 567 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 567 40 41, g32p_row17_traceSegment_051_0567_0040, g32p_row17_traceSegment_051_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_051 486 162 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 486 81 81, g32p_row17_traceSegment_051_0486_0081, g32p_row17_traceSegment_051_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_051 324 324 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 324 162 162, g32p_row17_traceSegment_051_0324_0162, g32p_row17_traceSegment_051_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_051 0 648 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 0 324 324, g32p_row17_traceSegment_051_0000_0324, g32p_row17_traceSegment_051_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 648 10 10, g32p_row17_traceSegment_051_0648_0010, g32p_row17_traceSegment_051_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 668 10 10, g32p_row17_traceSegment_051_0668_0010, g32p_row17_traceSegment_051_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 648 20 20, g32p_row17_traceSegment_051_0648_0020, g32p_row17_traceSegment_051_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 688 10 10, g32p_row17_traceSegment_051_0688_0010, g32p_row17_traceSegment_051_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 708 10 11, g32p_row17_traceSegment_051_0708_0010, g32p_row17_traceSegment_051_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 688 20 21, g32p_row17_traceSegment_051_0688_0020, g32p_row17_traceSegment_051_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 648 40 41, g32p_row17_traceSegment_051_0648_0040, g32p_row17_traceSegment_051_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 739 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 729 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 729 10 10, g32p_row17_traceSegment_051_0729_0010, g32p_row17_traceSegment_051_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 749 10 10, g32p_row17_traceSegment_051_0749_0010, g32p_row17_traceSegment_051_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 729 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 729 20 20, g32p_row17_traceSegment_051_0729_0020, g32p_row17_traceSegment_051_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 769 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 769 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 769 10 10, g32p_row17_traceSegment_051_0769_0010, g32p_row17_traceSegment_051_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 789 10 11, g32p_row17_traceSegment_051_0789_0010, g32p_row17_traceSegment_051_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 769 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 769 20 21, g32p_row17_traceSegment_051_0769_0020, g32p_row17_traceSegment_051_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 729 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 729 40 41, g32p_row17_traceSegment_051_0729_0040, g32p_row17_traceSegment_051_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_051 648 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 648 81 81, g32p_row17_traceSegment_051_0648_0081, g32p_row17_traceSegment_051_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 820 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 810 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 810 10 10, g32p_row17_traceSegment_051_0810_0010, g32p_row17_traceSegment_051_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 840 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 830 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 830 10 10, g32p_row17_traceSegment_051_0830_0010, g32p_row17_traceSegment_051_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 810 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 810 20 20, g32p_row17_traceSegment_051_0810_0020, g32p_row17_traceSegment_051_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 850 10 10, g32p_row17_traceSegment_051_0850_0010, g32p_row17_traceSegment_051_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 870 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 870 21 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 870 10 11, g32p_row17_traceSegment_051_0870_0010, g32p_row17_traceSegment_051_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 850 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 850 20 21, g32p_row17_traceSegment_051_0850_0020, g32p_row17_traceSegment_051_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 810 81 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 810 40 41, g32p_row17_traceSegment_051_0810_0040, g32p_row17_traceSegment_051_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 891 10 10, g32p_row17_traceSegment_051_0891_0010, g32p_row17_traceSegment_051_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 911 10 10, g32p_row17_traceSegment_051_0911_0010, g32p_row17_traceSegment_051_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 891 20 20, g32p_row17_traceSegment_051_0891_0020, g32p_row17_traceSegment_051_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 931 10 10, g32p_row17_traceSegment_051_0931_0010, g32p_row17_traceSegment_051_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 951 10 11, g32p_row17_traceSegment_051_0951_0010, g32p_row17_traceSegment_051_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 931 20 21, g32p_row17_traceSegment_051_0931_0020, g32p_row17_traceSegment_051_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 891 40 41, g32p_row17_traceSegment_051_0891_0040, g32p_row17_traceSegment_051_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_051 810 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 810 81 81, g32p_row17_traceSegment_051_0810_0081, g32p_row17_traceSegment_051_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_051 648 324 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 648 162 162, g32p_row17_traceSegment_051_0648_0162, g32p_row17_traceSegment_051_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 972 10 10, g32p_row17_traceSegment_051_0972_0010, g32p_row17_traceSegment_051_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 992 10 10, g32p_row17_traceSegment_051_0992_0010, g32p_row17_traceSegment_051_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 972 20 20, g32p_row17_traceSegment_051_0972_0020, g32p_row17_traceSegment_051_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1012 10 10, g32p_row17_traceSegment_051_1012_0010, g32p_row17_traceSegment_051_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1032 10 11, g32p_row17_traceSegment_051_1032_0010, g32p_row17_traceSegment_051_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1012 20 21, g32p_row17_traceSegment_051_1012_0020, g32p_row17_traceSegment_051_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 972 40 41, g32p_row17_traceSegment_051_0972_0040, g32p_row17_traceSegment_051_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1053 10 10, g32p_row17_traceSegment_051_1053_0010, g32p_row17_traceSegment_051_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1073 10 10, g32p_row17_traceSegment_051_1073_0010, g32p_row17_traceSegment_051_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1053 20 20, g32p_row17_traceSegment_051_1053_0020, g32p_row17_traceSegment_051_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1093 10 10, g32p_row17_traceSegment_051_1093_0010, g32p_row17_traceSegment_051_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1113 10 11, g32p_row17_traceSegment_051_1113_0010, g32p_row17_traceSegment_051_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1093 20 21, g32p_row17_traceSegment_051_1093_0020, g32p_row17_traceSegment_051_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1053 40 41, g32p_row17_traceSegment_051_1053_0040, g32p_row17_traceSegment_051_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_051 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 972 81 81, g32p_row17_traceSegment_051_0972_0081, g32p_row17_traceSegment_051_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1144 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 1134 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1134 10 10, g32p_row17_traceSegment_051_1134_0010, g32p_row17_traceSegment_051_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1154 10 10, g32p_row17_traceSegment_051_1154_0010, g32p_row17_traceSegment_051_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 1134 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1134 20 20, g32p_row17_traceSegment_051_1134_0020, g32p_row17_traceSegment_051_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1184 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 1174 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1174 10 10, g32p_row17_traceSegment_051_1174_0010, g32p_row17_traceSegment_051_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1194 10 11, g32p_row17_traceSegment_051_1194_0010, g32p_row17_traceSegment_051_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 1174 41 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1174 20 21, g32p_row17_traceSegment_051_1174_0020, g32p_row17_traceSegment_051_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 1134 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1134 40 41, g32p_row17_traceSegment_051_1134_0040, g32p_row17_traceSegment_051_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1215 10 10, g32p_row17_traceSegment_051_1215_0010, g32p_row17_traceSegment_051_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1245 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 1235 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1235 10 10, g32p_row17_traceSegment_051_1235_0010, g32p_row17_traceSegment_051_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_051 1215 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1215 20 20, g32p_row17_traceSegment_051_1215_0020, g32p_row17_traceSegment_051_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_051 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1255 10 10, g32p_row17_traceSegment_051_1255_0010, g32p_row17_traceSegment_051_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_051 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_051 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_051_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_051 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1275 10 11, g32p_row17_traceSegment_051_1275_0010, g32p_row17_traceSegment_051_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_051 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1255 20 21, g32p_row17_traceSegment_051_1255_0020, g32p_row17_traceSegment_051_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_051 1215 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1215 40 41, g32p_row17_traceSegment_051_1215_0040, g32p_row17_traceSegment_051_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_051_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_051 1134 162 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 1134 81 81, g32p_row17_traceSegment_051_1134_0081, g32p_row17_traceSegment_051_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_051 972 324 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 972 162 162, g32p_row17_traceSegment_051_0972_0162, g32p_row17_traceSegment_051_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_051 648 648 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 648 324 324, g32p_row17_traceSegment_051_0648_0324, g32p_row17_traceSegment_051_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_051_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_051 0 1296 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_051 0 648 648, g32p_row17_traceSegment_051_0000_0648, g32p_row17_traceSegment_051_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_051 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 51 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_051_0000_1296

end HodgeLean.Foundations.Program

end
end
