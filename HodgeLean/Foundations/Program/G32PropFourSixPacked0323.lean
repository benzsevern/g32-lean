import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_038 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 38 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_038_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 0 16 = [1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 24 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 16 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 16 8 9, g32p_row03_traceSegment_038_0016_0008, g32p_row03_traceSegment_038_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 0 33 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 0 16 17, g32p_row03_traceSegment_038_0000_0016, g32p_row03_traceSegment_038_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 33 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 41 9 = [4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 33 17 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 33 8 9, g32p_row03_traceSegment_038_0033_0008, g32p_row03_traceSegment_038_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 50 8 = [4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 58 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 50 17 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 50 8 9, g32p_row03_traceSegment_038_0050_0008, g32p_row03_traceSegment_038_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 33 34 = [10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 33 17 17, g32p_row03_traceSegment_038_0033_0017, g32p_row03_traceSegment_038_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 0 67 = [11, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 0 33 34, g32p_row03_traceSegment_038_0000_0033, g32p_row03_traceSegment_038_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 67 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 75 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 67 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 67 8 9, g32p_row03_traceSegment_038_0067_0008, g32p_row03_traceSegment_038_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 84 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 92 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 84 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 84 8 9, g32p_row03_traceSegment_038_0084_0008, g32p_row03_traceSegment_038_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 67 34 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 67 17 17, g32p_row03_traceSegment_038_0067_0017, g32p_row03_traceSegment_038_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 101 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 109 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 101 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 101 8 9, g32p_row03_traceSegment_038_0101_0008, g32p_row03_traceSegment_038_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 118 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 126 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 118 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 118 8 9, g32p_row03_traceSegment_038_0118_0008, g32p_row03_traceSegment_038_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 101 34 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 101 17 17, g32p_row03_traceSegment_038_0101_0017, g32p_row03_traceSegment_038_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 67 68 = [2, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 67 34 34, g32p_row03_traceSegment_038_0067_0034, g32p_row03_traceSegment_038_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 0 135 = [13, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 0 67 68, g32p_row03_traceSegment_038_0000_0067, g32p_row03_traceSegment_038_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 135 16 = [5] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 151 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 159 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 151 17 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 151 8 9, g32p_row03_traceSegment_038_0151_0008, g32p_row03_traceSegment_038_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 135 33 = [9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 135 16 17, g32p_row03_traceSegment_038_0135_0016, g32p_row03_traceSegment_038_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 176 9 = [3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 168 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 168 8 9, g32p_row03_traceSegment_038_0168_0008, g32p_row03_traceSegment_038_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 185 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 193 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 185 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 185 8 9, g32p_row03_traceSegment_038_0185_0008, g32p_row03_traceSegment_038_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 168 34 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 168 17 17, g32p_row03_traceSegment_038_0168_0017, g32p_row03_traceSegment_038_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 135 67 = [14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 135 33 34, g32p_row03_traceSegment_038_0135_0033, g32p_row03_traceSegment_038_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 202 8 9, g32p_row03_traceSegment_038_0202_0008, g32p_row03_traceSegment_038_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 219 8 9, g32p_row03_traceSegment_038_0219_0008, g32p_row03_traceSegment_038_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 202 17 17, g32p_row03_traceSegment_038_0202_0017, g32p_row03_traceSegment_038_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 236 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 244 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 236 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 236 8 9, g32p_row03_traceSegment_038_0236_0008, g32p_row03_traceSegment_038_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 261 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 253 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 253 8 9, g32p_row03_traceSegment_038_0253_0008, g32p_row03_traceSegment_038_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 236 34 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 236 17 17, g32p_row03_traceSegment_038_0236_0017, g32p_row03_traceSegment_038_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 202 68 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 202 34 34, g32p_row03_traceSegment_038_0202_0034, g32p_row03_traceSegment_038_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 135 135 = [14, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 135 67 68, g32p_row03_traceSegment_038_0135_0067, g32p_row03_traceSegment_038_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 0 270 = [27, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 0 135 135, g32p_row03_traceSegment_038_0000_0135, g32p_row03_traceSegment_038_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 270 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 294 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 286 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 286 8 9, g32p_row03_traceSegment_038_0286_0008, g32p_row03_traceSegment_038_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 270 33 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 270 16 17, g32p_row03_traceSegment_038_0270_0016, g32p_row03_traceSegment_038_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 311 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 303 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 303 8 9, g32p_row03_traceSegment_038_0303_0008, g32p_row03_traceSegment_038_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 320 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 328 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 320 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 320 8 9, g32p_row03_traceSegment_038_0320_0008, g32p_row03_traceSegment_038_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 303 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 303 17 17, g32p_row03_traceSegment_038_0303_0017, g32p_row03_traceSegment_038_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 270 67 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 270 33 34, g32p_row03_traceSegment_038_0270_0033, g32p_row03_traceSegment_038_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 337 8 9, g32p_row03_traceSegment_038_0337_0008, g32p_row03_traceSegment_038_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 362 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 354 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 354 8 9, g32p_row03_traceSegment_038_0354_0008, g32p_row03_traceSegment_038_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 337 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 337 17 17, g32p_row03_traceSegment_038_0337_0017, g32p_row03_traceSegment_038_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 371 8 9, g32p_row03_traceSegment_038_0371_0008, g32p_row03_traceSegment_038_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 388 8 9, g32p_row03_traceSegment_038_0388_0008, g32p_row03_traceSegment_038_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 371 17 17, g32p_row03_traceSegment_038_0371_0017, g32p_row03_traceSegment_038_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 337 68 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 337 34 34, g32p_row03_traceSegment_038_0337_0034, g32p_row03_traceSegment_038_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 270 135 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 270 67 68, g32p_row03_traceSegment_038_0270_0067, g32p_row03_traceSegment_038_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 405 16 = [5] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 421 8 = [5] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 429 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 421 17 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 421 8 9, g32p_row03_traceSegment_038_0421_0008, g32p_row03_traceSegment_038_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 405 33 = [11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 405 16 17, g32p_row03_traceSegment_038_0405_0016, g32p_row03_traceSegment_038_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 438 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 446 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 438 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 438 8 9, g32p_row03_traceSegment_038_0438_0008, g32p_row03_traceSegment_038_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 455 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 463 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 455 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 455 8 9, g32p_row03_traceSegment_038_0455_0008, g32p_row03_traceSegment_038_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 438 34 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 438 17 17, g32p_row03_traceSegment_038_0438_0017, g32p_row03_traceSegment_038_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 405 67 = [16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 405 33 34, g32p_row03_traceSegment_038_0405_0033, g32p_row03_traceSegment_038_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 472 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 480 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 472 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 472 8 9, g32p_row03_traceSegment_038_0472_0008, g32p_row03_traceSegment_038_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 489 8 9, g32p_row03_traceSegment_038_0489_0008, g32p_row03_traceSegment_038_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 472 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 472 17 17, g32p_row03_traceSegment_038_0472_0017, g32p_row03_traceSegment_038_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 506 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 506 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 506 8 9, g32p_row03_traceSegment_038_0506_0008, g32p_row03_traceSegment_038_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 531 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 523 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 523 8 9, g32p_row03_traceSegment_038_0523_0008, g32p_row03_traceSegment_038_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 506 34 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 506 17 17, g32p_row03_traceSegment_038_0506_0017, g32p_row03_traceSegment_038_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 472 68 = [3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 472 34 34, g32p_row03_traceSegment_038_0472_0034, g32p_row03_traceSegment_038_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 405 135 = [19, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 405 67 68, g32p_row03_traceSegment_038_0405_0067, g32p_row03_traceSegment_038_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 270 270 = [19, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 270 135 135, g32p_row03_traceSegment_038_0270_0135, g32p_row03_traceSegment_038_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_038 0 540 = [46, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 0 270 270, g32p_row03_traceSegment_038_0000_0270, g32p_row03_traceSegment_038_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 540 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 556 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 556 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 556 8 9, g32p_row03_traceSegment_038_0556_0008, g32p_row03_traceSegment_038_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 540 33 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 540 16 17, g32p_row03_traceSegment_038_0540_0016, g32p_row03_traceSegment_038_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 573 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 573 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 573 8 9, g32p_row03_traceSegment_038_0573_0008, g32p_row03_traceSegment_038_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 590 8 9, g32p_row03_traceSegment_038_0590_0008, g32p_row03_traceSegment_038_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 573 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 573 17 17, g32p_row03_traceSegment_038_0573_0017, g32p_row03_traceSegment_038_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 540 67 = [1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 540 33 34, g32p_row03_traceSegment_038_0540_0033, g32p_row03_traceSegment_038_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 607 8 9, g32p_row03_traceSegment_038_0607_0008, g32p_row03_traceSegment_038_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 632 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 624 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 624 8 9, g32p_row03_traceSegment_038_0624_0008, g32p_row03_traceSegment_038_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 607 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 607 17 17, g32p_row03_traceSegment_038_0607_0017, g32p_row03_traceSegment_038_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 641 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 649 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 641 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 641 8 9, g32p_row03_traceSegment_038_0641_0008, g32p_row03_traceSegment_038_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 658 8 9, g32p_row03_traceSegment_038_0658_0008, g32p_row03_traceSegment_038_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 641 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 641 17 17, g32p_row03_traceSegment_038_0641_0017, g32p_row03_traceSegment_038_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 607 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 607 34 34, g32p_row03_traceSegment_038_0607_0034, g32p_row03_traceSegment_038_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 540 135 = [1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 540 67 68, g32p_row03_traceSegment_038_0540_0067, g32p_row03_traceSegment_038_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 675 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 691 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 691 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 691 8 9, g32p_row03_traceSegment_038_0691_0008, g32p_row03_traceSegment_038_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 675 33 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 675 16 17, g32p_row03_traceSegment_038_0675_0016, g32p_row03_traceSegment_038_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 708 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 716 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 708 17 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 708 8 9, g32p_row03_traceSegment_038_0708_0008, g32p_row03_traceSegment_038_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 725 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 725 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 725 8 9, g32p_row03_traceSegment_038_0725_0008, g32p_row03_traceSegment_038_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 708 34 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 708 17 17, g32p_row03_traceSegment_038_0708_0017, g32p_row03_traceSegment_038_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 675 67 = [1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 675 33 34, g32p_row03_traceSegment_038_0675_0033, g32p_row03_traceSegment_038_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 742 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 750 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 742 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 742 8 9, g32p_row03_traceSegment_038_0742_0008, g32p_row03_traceSegment_038_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 759 8 9, g32p_row03_traceSegment_038_0759_0008, g32p_row03_traceSegment_038_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 742 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 742 17 17, g32p_row03_traceSegment_038_0742_0017, g32p_row03_traceSegment_038_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 784 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 776 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 776 8 9, g32p_row03_traceSegment_038_0776_0008, g32p_row03_traceSegment_038_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 801 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 793 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 793 8 9, g32p_row03_traceSegment_038_0793_0008, g32p_row03_traceSegment_038_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 776 34 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 776 17 17, g32p_row03_traceSegment_038_0776_0017, g32p_row03_traceSegment_038_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 742 68 = [2, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 742 34 34, g32p_row03_traceSegment_038_0742_0034, g32p_row03_traceSegment_038_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 675 135 = [3, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 675 67 68, g32p_row03_traceSegment_038_0675_0067, g32p_row03_traceSegment_038_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 540 270 = [4, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 540 135 135, g32p_row03_traceSegment_038_0540_0135, g32p_row03_traceSegment_038_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 810 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 826 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 826 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 826 8 9, g32p_row03_traceSegment_038_0826_0008, g32p_row03_traceSegment_038_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 810 33 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 810 16 17, g32p_row03_traceSegment_038_0810_0016, g32p_row03_traceSegment_038_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 843 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 843 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 843 8 9, g32p_row03_traceSegment_038_0843_0008, g32p_row03_traceSegment_038_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 860 8 9, g32p_row03_traceSegment_038_0860_0008, g32p_row03_traceSegment_038_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 843 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 843 17 17, g32p_row03_traceSegment_038_0843_0017, g32p_row03_traceSegment_038_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 810 67 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 810 33 34, g32p_row03_traceSegment_038_0810_0033, g32p_row03_traceSegment_038_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 877 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 885 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 877 17 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 877 8 9, g32p_row03_traceSegment_038_0877_0008, g32p_row03_traceSegment_038_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 894 8 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 894 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 894 8 9, g32p_row03_traceSegment_038_0894_0008, g32p_row03_traceSegment_038_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 877 34 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 877 17 17, g32p_row03_traceSegment_038_0877_0017, g32p_row03_traceSegment_038_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 919 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 911 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 911 8 9, g32p_row03_traceSegment_038_0911_0008, g32p_row03_traceSegment_038_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 936 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 928 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 928 8 9, g32p_row03_traceSegment_038_0928_0008, g32p_row03_traceSegment_038_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 911 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 911 17 17, g32p_row03_traceSegment_038_0911_0017, g32p_row03_traceSegment_038_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 877 68 = [4, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 877 34 34, g32p_row03_traceSegment_038_0877_0034, g32p_row03_traceSegment_038_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 810 135 = [5, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 810 67 68, g32p_row03_traceSegment_038_0810_0067, g32p_row03_traceSegment_038_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 945 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 961 8 9, g32p_row03_traceSegment_038_0961_0008, g32p_row03_traceSegment_038_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 945 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 945 16 17, g32p_row03_traceSegment_038_0945_0016, g32p_row03_traceSegment_038_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 978 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 986 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 978 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 978 8 9, g32p_row03_traceSegment_038_0978_0008, g32p_row03_traceSegment_038_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 995 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 995 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 995 8 9, g32p_row03_traceSegment_038_0995_0008, g32p_row03_traceSegment_038_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 978 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 978 17 17, g32p_row03_traceSegment_038_0978_0017, g32p_row03_traceSegment_038_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 945 67 = [3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 945 33 34, g32p_row03_traceSegment_038_0945_0033, g32p_row03_traceSegment_038_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1012 8 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1020 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1012 17 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1012 8 9, g32p_row03_traceSegment_038_1012_0008, g32p_row03_traceSegment_038_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1037 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1029 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1029 8 9, g32p_row03_traceSegment_038_1029_0008, g32p_row03_traceSegment_038_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1012 34 = [3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1012 17 17, g32p_row03_traceSegment_038_1012_0017, g32p_row03_traceSegment_038_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1046 8 9, g32p_row03_traceSegment_038_1046_0008, g32p_row03_traceSegment_038_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1071 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1063 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1063 8 9, g32p_row03_traceSegment_038_1063_0008, g32p_row03_traceSegment_038_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1046 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1046 17 17, g32p_row03_traceSegment_038_1046_0017, g32p_row03_traceSegment_038_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 1012 68 = [4, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1012 34 34, g32p_row03_traceSegment_038_1012_0034, g32p_row03_traceSegment_038_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 945 135 = [7, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 945 67 68, g32p_row03_traceSegment_038_0945_0067, g32p_row03_traceSegment_038_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 810 270 = [12, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 810 135 135, g32p_row03_traceSegment_038_0810_0135, g32p_row03_traceSegment_038_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_038 540 540 = [16, 0, 0, 28] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 540 270 270, g32p_row03_traceSegment_038_0540_0270, g32p_row03_traceSegment_038_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_038 0 1080 = [62, 0, 0, 58] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 0 540 540, g32p_row03_traceSegment_038_0000_0540, g32p_row03_traceSegment_038_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1096 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1096 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1096 8 9, g32p_row03_traceSegment_038_1096_0008, g32p_row03_traceSegment_038_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 1080 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1080 16 17, g32p_row03_traceSegment_038_1080_0016, g32p_row03_traceSegment_038_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1121 9 = [3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1113 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1113 8 9, g32p_row03_traceSegment_038_1113_0008, g32p_row03_traceSegment_038_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1138 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1130 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1130 8 9, g32p_row03_traceSegment_038_1130_0008, g32p_row03_traceSegment_038_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1113 34 = [4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1113 17 17, g32p_row03_traceSegment_038_1113_0017, g32p_row03_traceSegment_038_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 1080 67 = [6, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1080 33 34, g32p_row03_traceSegment_038_1080_0033, g32p_row03_traceSegment_038_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1147 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1147 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1147 8 9, g32p_row03_traceSegment_038_1147_0008, g32p_row03_traceSegment_038_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1164 8 9, g32p_row03_traceSegment_038_1164_0008, g32p_row03_traceSegment_038_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1147 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1147 17 17, g32p_row03_traceSegment_038_1147_0017, g32p_row03_traceSegment_038_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1181 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1189 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1181 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1181 8 9, g32p_row03_traceSegment_038_1181_0008, g32p_row03_traceSegment_038_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1198 8 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1206 9 = [3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1198 17 = [4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1198 8 9, g32p_row03_traceSegment_038_1198_0008, g32p_row03_traceSegment_038_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1181 34 = [7, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1181 17 17, g32p_row03_traceSegment_038_1181_0017, g32p_row03_traceSegment_038_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 1147 68 = [8, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1147 34 34, g32p_row03_traceSegment_038_1147_0034, g32p_row03_traceSegment_038_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 1080 135 = [14, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1080 67 68, g32p_row03_traceSegment_038_1080_0067, g32p_row03_traceSegment_038_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 1215 16 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1239 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1231 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1231 8 9, g32p_row03_traceSegment_038_1231_0008, g32p_row03_traceSegment_038_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 1215 33 = [3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1215 16 17, g32p_row03_traceSegment_038_1215_0016, g32p_row03_traceSegment_038_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1248 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1256 9 = [3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1248 17 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1248 8 9, g32p_row03_traceSegment_038_1248_0008, g32p_row03_traceSegment_038_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1265 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1273 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1265 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1265 8 9, g32p_row03_traceSegment_038_1265_0008, g32p_row03_traceSegment_038_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1248 34 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1248 17 17, g32p_row03_traceSegment_038_1248_0017, g32p_row03_traceSegment_038_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 1215 67 = [11, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1215 33 34, g32p_row03_traceSegment_038_1215_0033, g32p_row03_traceSegment_038_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1282 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1290 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1282 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1282 8 9, g32p_row03_traceSegment_038_1282_0008, g32p_row03_traceSegment_038_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1299 8 9, g32p_row03_traceSegment_038_1299_0008, g32p_row03_traceSegment_038_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1282 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1282 17 17, g32p_row03_traceSegment_038_1282_0017, g32p_row03_traceSegment_038_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1316 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1324 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1316 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1316 8 9, g32p_row03_traceSegment_038_1316_0008, g32p_row03_traceSegment_038_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1333 8 9, g32p_row03_traceSegment_038_1333_0008, g32p_row03_traceSegment_038_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1316 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1316 17 17, g32p_row03_traceSegment_038_1316_0017, g32p_row03_traceSegment_038_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 1282 68 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1282 34 34, g32p_row03_traceSegment_038_1282_0034, g32p_row03_traceSegment_038_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 1215 135 = [16, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1215 67 68, g32p_row03_traceSegment_038_1215_0067, g32p_row03_traceSegment_038_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 1080 270 = [30, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1080 135 135, g32p_row03_traceSegment_038_1080_0135, g32p_row03_traceSegment_038_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 1350 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1366 8 9, g32p_row03_traceSegment_038_1366_0008, g32p_row03_traceSegment_038_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 1350 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1350 16 17, g32p_row03_traceSegment_038_1350_0016, g32p_row03_traceSegment_038_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1383 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1383 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1383 8 9, g32p_row03_traceSegment_038_1383_0008, g32p_row03_traceSegment_038_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1408 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1400 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1400 8 9, g32p_row03_traceSegment_038_1400_0008, g32p_row03_traceSegment_038_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1383 34 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1383 17 17, g32p_row03_traceSegment_038_1383_0017, g32p_row03_traceSegment_038_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 1350 67 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1350 33 34, g32p_row03_traceSegment_038_1350_0033, g32p_row03_traceSegment_038_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1417 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1417 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1417 8 9, g32p_row03_traceSegment_038_1417_0008, g32p_row03_traceSegment_038_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1442 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1434 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1434 8 9, g32p_row03_traceSegment_038_1434_0008, g32p_row03_traceSegment_038_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1417 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1417 17 17, g32p_row03_traceSegment_038_1417_0017, g32p_row03_traceSegment_038_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1451 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1459 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1451 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1451 8 9, g32p_row03_traceSegment_038_1451_0008, g32p_row03_traceSegment_038_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1468 8 9, g32p_row03_traceSegment_038_1468_0008, g32p_row03_traceSegment_038_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1451 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1451 17 17, g32p_row03_traceSegment_038_1451_0017, g32p_row03_traceSegment_038_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 1417 68 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1417 34 34, g32p_row03_traceSegment_038_1417_0034, g32p_row03_traceSegment_038_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 1350 135 = [2, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1350 67 68, g32p_row03_traceSegment_038_1350_0067, g32p_row03_traceSegment_038_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 1485 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1501 8 9, g32p_row03_traceSegment_038_1501_0008, g32p_row03_traceSegment_038_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 1485 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1485 16 17, g32p_row03_traceSegment_038_1485_0016, g32p_row03_traceSegment_038_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1518 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1526 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1518 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1518 8 9, g32p_row03_traceSegment_038_1518_0008, g32p_row03_traceSegment_038_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1535 8 9, g32p_row03_traceSegment_038_1535_0008, g32p_row03_traceSegment_038_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1518 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1518 17 17, g32p_row03_traceSegment_038_1518_0017, g32p_row03_traceSegment_038_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 1485 67 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1485 33 34, g32p_row03_traceSegment_038_1485_0033, g32p_row03_traceSegment_038_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1552 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1552 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1552 8 9, g32p_row03_traceSegment_038_1552_0008, g32p_row03_traceSegment_038_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1569 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1577 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1569 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1569 8 9, g32p_row03_traceSegment_038_1569_0008, g32p_row03_traceSegment_038_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1552 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1552 17 17, g32p_row03_traceSegment_038_1552_0017, g32p_row03_traceSegment_038_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1586 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1594 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1586 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1586 8 9, g32p_row03_traceSegment_038_1586_0008, g32p_row03_traceSegment_038_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1603 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1611 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1603 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1603 8 9, g32p_row03_traceSegment_038_1603_0008, g32p_row03_traceSegment_038_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1586 34 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1586 17 17, g32p_row03_traceSegment_038_1586_0017, g32p_row03_traceSegment_038_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 1552 68 = [1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1552 34 34, g32p_row03_traceSegment_038_1552_0034, g32p_row03_traceSegment_038_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 1485 135 = [2, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1485 67 68, g32p_row03_traceSegment_038_1485_0067, g32p_row03_traceSegment_038_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 1350 270 = [4, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1350 135 135, g32p_row03_traceSegment_038_1350_0135, g32p_row03_traceSegment_038_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_038 1080 540 = [34, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1080 270 270, g32p_row03_traceSegment_038_1080_0270, g32p_row03_traceSegment_038_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 1620 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1636 8 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1644 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1636 17 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1636 8 9, g32p_row03_traceSegment_038_1636_0008, g32p_row03_traceSegment_038_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 1620 33 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1620 16 17, g32p_row03_traceSegment_038_1620_0016, g32p_row03_traceSegment_038_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1653 8 9, g32p_row03_traceSegment_038_1653_0008, g32p_row03_traceSegment_038_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1670 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1670 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1670 8 9, g32p_row03_traceSegment_038_1670_0008, g32p_row03_traceSegment_038_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1653 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1653 17 17, g32p_row03_traceSegment_038_1653_0017, g32p_row03_traceSegment_038_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 1620 67 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1620 33 34, g32p_row03_traceSegment_038_1620_0033, g32p_row03_traceSegment_038_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1687 8 9, g32p_row03_traceSegment_038_1687_0008, g32p_row03_traceSegment_038_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1704 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1712 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1704 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1704 8 9, g32p_row03_traceSegment_038_1704_0008, g32p_row03_traceSegment_038_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1687 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1687 17 17, g32p_row03_traceSegment_038_1687_0017, g32p_row03_traceSegment_038_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1721 8 9, g32p_row03_traceSegment_038_1721_0008, g32p_row03_traceSegment_038_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1738 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1746 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1738 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1738 8 9, g32p_row03_traceSegment_038_1738_0008, g32p_row03_traceSegment_038_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1721 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1721 17 17, g32p_row03_traceSegment_038_1721_0017, g32p_row03_traceSegment_038_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 1687 68 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1687 34 34, g32p_row03_traceSegment_038_1687_0034, g32p_row03_traceSegment_038_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 1620 135 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1620 67 68, g32p_row03_traceSegment_038_1620_0067, g32p_row03_traceSegment_038_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 1755 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1779 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1771 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1771 8 9, g32p_row03_traceSegment_038_1771_0008, g32p_row03_traceSegment_038_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 1755 33 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1755 16 17, g32p_row03_traceSegment_038_1755_0016, g32p_row03_traceSegment_038_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1796 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1788 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1788 8 9, g32p_row03_traceSegment_038_1788_0008, g32p_row03_traceSegment_038_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1805 8 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1813 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1805 17 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1805 8 9, g32p_row03_traceSegment_038_1805_0008, g32p_row03_traceSegment_038_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1788 34 = [1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1788 17 17, g32p_row03_traceSegment_038_1788_0017, g32p_row03_traceSegment_038_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 1755 67 = [2, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1755 33 34, g32p_row03_traceSegment_038_1755_0033, g32p_row03_traceSegment_038_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1822 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1830 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1822 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1822 8 9, g32p_row03_traceSegment_038_1822_0008, g32p_row03_traceSegment_038_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1839 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1847 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1839 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1839 8 9, g32p_row03_traceSegment_038_1839_0008, g32p_row03_traceSegment_038_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1822 34 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1822 17 17, g32p_row03_traceSegment_038_1822_0017, g32p_row03_traceSegment_038_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1856 8 9, g32p_row03_traceSegment_038_1856_0008, g32p_row03_traceSegment_038_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1873 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1873 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1873 8 9, g32p_row03_traceSegment_038_1873_0008, g32p_row03_traceSegment_038_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1856 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1856 17 17, g32p_row03_traceSegment_038_1856_0017, g32p_row03_traceSegment_038_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 1822 68 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1822 34 34, g32p_row03_traceSegment_038_1822_0034, g32p_row03_traceSegment_038_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 1755 135 = [2, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1755 67 68, g32p_row03_traceSegment_038_1755_0067, g32p_row03_traceSegment_038_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 1620 270 = [2, 0, 0, 29] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1620 135 135, g32p_row03_traceSegment_038_1620_0135, g32p_row03_traceSegment_038_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1906 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1914 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1906 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1906 8 9, g32p_row03_traceSegment_038_1906_0008, g32p_row03_traceSegment_038_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 1890 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1890 16 17, g32p_row03_traceSegment_038_1890_0016, g32p_row03_traceSegment_038_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1923 8 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1931 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1923 17 = [1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1923 8 9, g32p_row03_traceSegment_038_1923_0008, g32p_row03_traceSegment_038_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1940 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1940 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1940 8 9, g32p_row03_traceSegment_038_1940_0008, g32p_row03_traceSegment_038_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1923 34 = [1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1923 17 17, g32p_row03_traceSegment_038_1923_0017, g32p_row03_traceSegment_038_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 1890 67 = [1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1890 33 34, g32p_row03_traceSegment_038_1890_0033, g32p_row03_traceSegment_038_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1957 8 9, g32p_row03_traceSegment_038_1957_0008, g32p_row03_traceSegment_038_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1982 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1974 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1974 8 9, g32p_row03_traceSegment_038_1974_0008, g32p_row03_traceSegment_038_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1957 34 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1957 17 17, g32p_row03_traceSegment_038_1957_0017, g32p_row03_traceSegment_038_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1991 8 9, g32p_row03_traceSegment_038_1991_0008, g32p_row03_traceSegment_038_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2008 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2016 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2008 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2008 8 9, g32p_row03_traceSegment_038_2008_0008, g32p_row03_traceSegment_038_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 1991 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1991 17 17, g32p_row03_traceSegment_038_1991_0017, g32p_row03_traceSegment_038_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 1957 68 = [1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1957 34 34, g32p_row03_traceSegment_038_1957_0034, g32p_row03_traceSegment_038_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 1890 135 = [2, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1890 67 68, g32p_row03_traceSegment_038_1890_0067, g32p_row03_traceSegment_038_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 2025 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2049 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2041 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2041 8 9, g32p_row03_traceSegment_038_2041_0008, g32p_row03_traceSegment_038_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 2025 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2025 16 17, g32p_row03_traceSegment_038_2025_0016, g32p_row03_traceSegment_038_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2058 8 9, g32p_row03_traceSegment_038_2058_0008, g32p_row03_traceSegment_038_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2075 8 9, g32p_row03_traceSegment_038_2075_0008, g32p_row03_traceSegment_038_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2058 17 17, g32p_row03_traceSegment_038_2058_0017, g32p_row03_traceSegment_038_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 2025 67 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2025 33 34, g32p_row03_traceSegment_038_2025_0033, g32p_row03_traceSegment_038_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2092 8 9, g32p_row03_traceSegment_038_2092_0008, g32p_row03_traceSegment_038_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2109 8 9, g32p_row03_traceSegment_038_2109_0008, g32p_row03_traceSegment_038_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2092 17 17, g32p_row03_traceSegment_038_2092_0017, g32p_row03_traceSegment_038_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2126 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2134 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2126 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2126 8 9, g32p_row03_traceSegment_038_2126_0008, g32p_row03_traceSegment_038_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2143 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2143 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2143 8 9, g32p_row03_traceSegment_038_2143_0008, g32p_row03_traceSegment_038_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2126 34 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2126 17 17, g32p_row03_traceSegment_038_2126_0017, g32p_row03_traceSegment_038_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 2092 68 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2092 34 34, g32p_row03_traceSegment_038_2092_0034, g32p_row03_traceSegment_038_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 2025 135 = [2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2025 67 68, g32p_row03_traceSegment_038_2025_0067, g32p_row03_traceSegment_038_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 1890 270 = [4, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1890 135 135, g32p_row03_traceSegment_038_1890_0135, g32p_row03_traceSegment_038_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_038 1620 540 = [6, 0, 0, 43] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1620 270 270, g32p_row03_traceSegment_038_1620_0270, g32p_row03_traceSegment_038_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_038_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_038 1080 1080 = [40, 0, 0, 64] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 1080 540 540, g32p_row03_traceSegment_038_1080_0540, g32p_row03_traceSegment_038_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_038 0 2160 = [102, 0, 0, 122] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 0 1080 1080, g32p_row03_traceSegment_038_0000_1080, g32p_row03_traceSegment_038_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 2160 16 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2176 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2176 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2176 8 9, g32p_row03_traceSegment_038_2176_0008, g32p_row03_traceSegment_038_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 2160 33 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2160 16 17, g32p_row03_traceSegment_038_2160_0016, g32p_row03_traceSegment_038_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2193 8 9, g32p_row03_traceSegment_038_2193_0008, g32p_row03_traceSegment_038_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2210 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2210 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2210 8 9, g32p_row03_traceSegment_038_2210_0008, g32p_row03_traceSegment_038_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2193 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2193 17 17, g32p_row03_traceSegment_038_2193_0017, g32p_row03_traceSegment_038_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 2160 67 = [4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2160 33 34, g32p_row03_traceSegment_038_2160_0033, g32p_row03_traceSegment_038_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2235 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2227 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2227 8 9, g32p_row03_traceSegment_038_2227_0008, g32p_row03_traceSegment_038_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2244 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2244 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2244 8 9, g32p_row03_traceSegment_038_2244_0008, g32p_row03_traceSegment_038_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2227 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2227 17 17, g32p_row03_traceSegment_038_2227_0017, g32p_row03_traceSegment_038_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2261 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2261 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2261 8 9, g32p_row03_traceSegment_038_2261_0008, g32p_row03_traceSegment_038_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2278 8 9, g32p_row03_traceSegment_038_2278_0008, g32p_row03_traceSegment_038_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2261 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2261 17 17, g32p_row03_traceSegment_038_2261_0017, g32p_row03_traceSegment_038_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 2227 68 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2227 34 34, g32p_row03_traceSegment_038_2227_0034, g32p_row03_traceSegment_038_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 2160 135 = [8, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2160 67 68, g32p_row03_traceSegment_038_2160_0067, g32p_row03_traceSegment_038_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2311 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2319 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2311 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2311 8 9, g32p_row03_traceSegment_038_2311_0008, g32p_row03_traceSegment_038_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 2295 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2295 16 17, g32p_row03_traceSegment_038_2295_0016, g32p_row03_traceSegment_038_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2328 8 9, g32p_row03_traceSegment_038_2328_0008, g32p_row03_traceSegment_038_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2345 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2353 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2345 17 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2345 8 9, g32p_row03_traceSegment_038_2345_0008, g32p_row03_traceSegment_038_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2328 34 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2328 17 17, g32p_row03_traceSegment_038_2328_0017, g32p_row03_traceSegment_038_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 2295 67 = [4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2295 33 34, g32p_row03_traceSegment_038_2295_0033, g32p_row03_traceSegment_038_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2370 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2362 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2362 8 9, g32p_row03_traceSegment_038_2362_0008, g32p_row03_traceSegment_038_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2387 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2379 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2379 8 9, g32p_row03_traceSegment_038_2379_0008, g32p_row03_traceSegment_038_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2362 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2362 17 17, g32p_row03_traceSegment_038_2362_0017, g32p_row03_traceSegment_038_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2404 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2396 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2396 8 9, g32p_row03_traceSegment_038_2396_0008, g32p_row03_traceSegment_038_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2421 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2413 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2413 8 9, g32p_row03_traceSegment_038_2413_0008, g32p_row03_traceSegment_038_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2396 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2396 17 17, g32p_row03_traceSegment_038_2396_0017, g32p_row03_traceSegment_038_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 2362 68 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2362 34 34, g32p_row03_traceSegment_038_2362_0034, g32p_row03_traceSegment_038_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 2295 135 = [8, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2295 67 68, g32p_row03_traceSegment_038_2295_0067, g32p_row03_traceSegment_038_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 2160 270 = [16, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2160 135 135, g32p_row03_traceSegment_038_2160_0135, g32p_row03_traceSegment_038_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2446 8 9, g32p_row03_traceSegment_038_2446_0008, g32p_row03_traceSegment_038_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2430 16 17, g32p_row03_traceSegment_038_2430_0016, g32p_row03_traceSegment_038_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2463 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2463 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2463 8 9, g32p_row03_traceSegment_038_2463_0008, g32p_row03_traceSegment_038_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2480 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2480 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2480 8 9, g32p_row03_traceSegment_038_2480_0008, g32p_row03_traceSegment_038_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2463 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2463 17 17, g32p_row03_traceSegment_038_2463_0017, g32p_row03_traceSegment_038_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 2430 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2430 33 34, g32p_row03_traceSegment_038_2430_0033, g32p_row03_traceSegment_038_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2505 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2497 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2497 8 9, g32p_row03_traceSegment_038_2497_0008, g32p_row03_traceSegment_038_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2514 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2514 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2514 8 9, g32p_row03_traceSegment_038_2514_0008, g32p_row03_traceSegment_038_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2497 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2497 17 17, g32p_row03_traceSegment_038_2497_0017, g32p_row03_traceSegment_038_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2539 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2531 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2531 8 9, g32p_row03_traceSegment_038_2531_0008, g32p_row03_traceSegment_038_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2548 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2556 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2548 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2548 8 9, g32p_row03_traceSegment_038_2548_0008, g32p_row03_traceSegment_038_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2531 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2531 17 17, g32p_row03_traceSegment_038_2531_0017, g32p_row03_traceSegment_038_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 2497 68 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2497 34 34, g32p_row03_traceSegment_038_2497_0034, g32p_row03_traceSegment_038_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 2430 135 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2430 67 68, g32p_row03_traceSegment_038_2430_0067, g32p_row03_traceSegment_038_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 2565 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2581 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2589 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2581 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2581 8 9, g32p_row03_traceSegment_038_2581_0008, g32p_row03_traceSegment_038_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 2565 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2565 16 17, g32p_row03_traceSegment_038_2565_0016, g32p_row03_traceSegment_038_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2598 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2598 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2598 8 9, g32p_row03_traceSegment_038_2598_0008, g32p_row03_traceSegment_038_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2615 8 9, g32p_row03_traceSegment_038_2615_0008, g32p_row03_traceSegment_038_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2598 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2598 17 17, g32p_row03_traceSegment_038_2598_0017, g32p_row03_traceSegment_038_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 2565 67 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2565 33 34, g32p_row03_traceSegment_038_2565_0033, g32p_row03_traceSegment_038_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2632 8 9, g32p_row03_traceSegment_038_2632_0008, g32p_row03_traceSegment_038_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2649 8 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2657 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2649 17 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2649 8 9, g32p_row03_traceSegment_038_2649_0008, g32p_row03_traceSegment_038_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2632 34 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2632 17 17, g32p_row03_traceSegment_038_2632_0017, g32p_row03_traceSegment_038_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2674 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2666 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2666 8 9, g32p_row03_traceSegment_038_2666_0008, g32p_row03_traceSegment_038_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2691 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2683 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2683 8 9, g32p_row03_traceSegment_038_2683_0008, g32p_row03_traceSegment_038_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2666 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2666 17 17, g32p_row03_traceSegment_038_2666_0017, g32p_row03_traceSegment_038_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 2632 68 = [5, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2632 34 34, g32p_row03_traceSegment_038_2632_0034, g32p_row03_traceSegment_038_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 2565 135 = [10, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2565 67 68, g32p_row03_traceSegment_038_2565_0067, g32p_row03_traceSegment_038_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 2430 270 = [17, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2430 135 135, g32p_row03_traceSegment_038_2430_0135, g32p_row03_traceSegment_038_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_038 2160 540 = [33, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2160 270 270, g32p_row03_traceSegment_038_2160_0270, g32p_row03_traceSegment_038_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2716 8 9, g32p_row03_traceSegment_038_2716_0008, g32p_row03_traceSegment_038_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2700 16 17, g32p_row03_traceSegment_038_2700_0016, g32p_row03_traceSegment_038_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2733 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2733 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2733 8 9, g32p_row03_traceSegment_038_2733_0008, g32p_row03_traceSegment_038_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2758 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2750 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2750 8 9, g32p_row03_traceSegment_038_2750_0008, g32p_row03_traceSegment_038_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2733 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2733 17 17, g32p_row03_traceSegment_038_2733_0017, g32p_row03_traceSegment_038_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 2700 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2700 33 34, g32p_row03_traceSegment_038_2700_0033, g32p_row03_traceSegment_038_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2767 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2767 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2767 8 9, g32p_row03_traceSegment_038_2767_0008, g32p_row03_traceSegment_038_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2792 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2784 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2784 8 9, g32p_row03_traceSegment_038_2784_0008, g32p_row03_traceSegment_038_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2767 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2767 17 17, g32p_row03_traceSegment_038_2767_0017, g32p_row03_traceSegment_038_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2801 8 9, g32p_row03_traceSegment_038_2801_0008, g32p_row03_traceSegment_038_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2818 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2818 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2818 8 9, g32p_row03_traceSegment_038_2818_0008, g32p_row03_traceSegment_038_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2801 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2801 17 17, g32p_row03_traceSegment_038_2801_0017, g32p_row03_traceSegment_038_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 2767 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2767 34 34, g32p_row03_traceSegment_038_2767_0034, g32p_row03_traceSegment_038_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 2700 135 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2700 67 68, g32p_row03_traceSegment_038_2700_0067, g32p_row03_traceSegment_038_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 2835 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2859 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2851 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2851 8 9, g32p_row03_traceSegment_038_2851_0008, g32p_row03_traceSegment_038_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 2835 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2835 16 17, g32p_row03_traceSegment_038_2835_0016, g32p_row03_traceSegment_038_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2868 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2868 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2868 8 9, g32p_row03_traceSegment_038_2868_0008, g32p_row03_traceSegment_038_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2885 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2893 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2885 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2885 8 9, g32p_row03_traceSegment_038_2885_0008, g32p_row03_traceSegment_038_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2868 34 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2868 17 17, g32p_row03_traceSegment_038_2868_0017, g32p_row03_traceSegment_038_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 2835 67 = [4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2835 33 34, g32p_row03_traceSegment_038_2835_0033, g32p_row03_traceSegment_038_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2902 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2910 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2902 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2902 8 9, g32p_row03_traceSegment_038_2902_0008, g32p_row03_traceSegment_038_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2919 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2919 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2919 8 9, g32p_row03_traceSegment_038_2919_0008, g32p_row03_traceSegment_038_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2902 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2902 17 17, g32p_row03_traceSegment_038_2902_0017, g32p_row03_traceSegment_038_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2944 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2936 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2936 8 9, g32p_row03_traceSegment_038_2936_0008, g32p_row03_traceSegment_038_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2953 8 9, g32p_row03_traceSegment_038_2953_0008, g32p_row03_traceSegment_038_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 2936 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2936 17 17, g32p_row03_traceSegment_038_2936_0017, g32p_row03_traceSegment_038_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 2902 68 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2902 34 34, g32p_row03_traceSegment_038_2902_0034, g32p_row03_traceSegment_038_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 2835 135 = [8, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2835 67 68, g32p_row03_traceSegment_038_2835_0067, g32p_row03_traceSegment_038_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 2700 270 = [13, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2700 135 135, g32p_row03_traceSegment_038_2700_0135, g32p_row03_traceSegment_038_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 2970 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 2994 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 2986 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2986 8 9, g32p_row03_traceSegment_038_2986_0008, g32p_row03_traceSegment_038_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 2970 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2970 16 17, g32p_row03_traceSegment_038_2970_0016, g32p_row03_traceSegment_038_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3003 8 9, g32p_row03_traceSegment_038_3003_0008, g32p_row03_traceSegment_038_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3020 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3020 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3020 8 9, g32p_row03_traceSegment_038_3020_0008, g32p_row03_traceSegment_038_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3003 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3003 17 17, g32p_row03_traceSegment_038_3003_0017, g32p_row03_traceSegment_038_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 2970 67 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2970 33 34, g32p_row03_traceSegment_038_2970_0033, g32p_row03_traceSegment_038_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3037 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3037 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3037 8 9, g32p_row03_traceSegment_038_3037_0008, g32p_row03_traceSegment_038_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3054 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3062 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3054 17 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3054 8 9, g32p_row03_traceSegment_038_3054_0008, g32p_row03_traceSegment_038_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3037 34 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3037 17 17, g32p_row03_traceSegment_038_3037_0017, g32p_row03_traceSegment_038_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3071 8 9, g32p_row03_traceSegment_038_3071_0008, g32p_row03_traceSegment_038_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3088 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3088 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3088 8 9, g32p_row03_traceSegment_038_3088_0008, g32p_row03_traceSegment_038_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3071 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3071 17 17, g32p_row03_traceSegment_038_3071_0017, g32p_row03_traceSegment_038_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 3037 68 = [1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3037 34 34, g32p_row03_traceSegment_038_3037_0034, g32p_row03_traceSegment_038_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 2970 135 = [2, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2970 67 68, g32p_row03_traceSegment_038_2970_0067, g32p_row03_traceSegment_038_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3121 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3121 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3121 8 9, g32p_row03_traceSegment_038_3121_0008, g32p_row03_traceSegment_038_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 3105 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3105 16 17, g32p_row03_traceSegment_038_3105_0016, g32p_row03_traceSegment_038_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3138 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3146 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3138 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3138 8 9, g32p_row03_traceSegment_038_3138_0008, g32p_row03_traceSegment_038_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3155 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3155 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3155 8 9, g32p_row03_traceSegment_038_3155_0008, g32p_row03_traceSegment_038_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3138 34 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3138 17 17, g32p_row03_traceSegment_038_3138_0017, g32p_row03_traceSegment_038_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 3105 67 = [1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3105 33 34, g32p_row03_traceSegment_038_3105_0033, g32p_row03_traceSegment_038_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3180 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3172 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3172 8 9, g32p_row03_traceSegment_038_3172_0008, g32p_row03_traceSegment_038_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3189 8 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3197 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3189 17 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3189 8 9, g32p_row03_traceSegment_038_3189_0008, g32p_row03_traceSegment_038_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3172 34 = [1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3172 17 17, g32p_row03_traceSegment_038_3172_0017, g32p_row03_traceSegment_038_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3206 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3206 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3206 8 9, g32p_row03_traceSegment_038_3206_0008, g32p_row03_traceSegment_038_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3223 8 9, g32p_row03_traceSegment_038_3223_0008, g32p_row03_traceSegment_038_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3206 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3206 17 17, g32p_row03_traceSegment_038_3206_0017, g32p_row03_traceSegment_038_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 3172 68 = [1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3172 34 34, g32p_row03_traceSegment_038_3172_0034, g32p_row03_traceSegment_038_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 3105 135 = [2, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3105 67 68, g32p_row03_traceSegment_038_3105_0067, g32p_row03_traceSegment_038_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 2970 270 = [4, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2970 135 135, g32p_row03_traceSegment_038_2970_0135, g32p_row03_traceSegment_038_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_038 2700 540 = [17, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2700 270 270, g32p_row03_traceSegment_038_2700_0270, g32p_row03_traceSegment_038_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_038 2160 1080 = [50, 0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2160 540 540, g32p_row03_traceSegment_038_2160_0540, g32p_row03_traceSegment_038_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 3240 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3256 8 9, g32p_row03_traceSegment_038_3256_0008, g32p_row03_traceSegment_038_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 3240 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3240 16 17, g32p_row03_traceSegment_038_3240_0016, g32p_row03_traceSegment_038_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3273 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3273 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3273 8 9, g32p_row03_traceSegment_038_3273_0008, g32p_row03_traceSegment_038_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3290 8 9, g32p_row03_traceSegment_038_3290_0008, g32p_row03_traceSegment_038_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3273 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3273 17 17, g32p_row03_traceSegment_038_3273_0017, g32p_row03_traceSegment_038_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 3240 67 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3240 33 34, g32p_row03_traceSegment_038_3240_0033, g32p_row03_traceSegment_038_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3307 8 9, g32p_row03_traceSegment_038_3307_0008, g32p_row03_traceSegment_038_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3324 8 9, g32p_row03_traceSegment_038_3324_0008, g32p_row03_traceSegment_038_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3307 17 17, g32p_row03_traceSegment_038_3307_0017, g32p_row03_traceSegment_038_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3341 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3349 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3341 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3341 8 9, g32p_row03_traceSegment_038_3341_0008, g32p_row03_traceSegment_038_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3358 8 9, g32p_row03_traceSegment_038_3358_0008, g32p_row03_traceSegment_038_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3341 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3341 17 17, g32p_row03_traceSegment_038_3341_0017, g32p_row03_traceSegment_038_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 3307 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3307 34 34, g32p_row03_traceSegment_038_3307_0034, g32p_row03_traceSegment_038_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 3240 135 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3240 67 68, g32p_row03_traceSegment_038_3240_0067, g32p_row03_traceSegment_038_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 3375 16 = [1, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3399 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3391 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3391 8 9, g32p_row03_traceSegment_038_3391_0008, g32p_row03_traceSegment_038_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 3375 33 = [1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3375 16 17, g32p_row03_traceSegment_038_3375_0016, g32p_row03_traceSegment_038_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3408 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3416 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3408 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3408 8 9, g32p_row03_traceSegment_038_3408_0008, g32p_row03_traceSegment_038_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3433 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3425 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3425 8 9, g32p_row03_traceSegment_038_3425_0008, g32p_row03_traceSegment_038_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3408 34 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3408 17 17, g32p_row03_traceSegment_038_3408_0017, g32p_row03_traceSegment_038_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 3375 67 = [2, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3375 33 34, g32p_row03_traceSegment_038_3375_0033, g32p_row03_traceSegment_038_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3442 8 9, g32p_row03_traceSegment_038_3442_0008, g32p_row03_traceSegment_038_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3467 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3459 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3459 8 9, g32p_row03_traceSegment_038_3459_0008, g32p_row03_traceSegment_038_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3442 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3442 17 17, g32p_row03_traceSegment_038_3442_0017, g32p_row03_traceSegment_038_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3476 8 9, g32p_row03_traceSegment_038_3476_0008, g32p_row03_traceSegment_038_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3493 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3501 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3493 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3493 8 9, g32p_row03_traceSegment_038_3493_0008, g32p_row03_traceSegment_038_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3476 34 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3476 17 17, g32p_row03_traceSegment_038_3476_0017, g32p_row03_traceSegment_038_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 3442 68 = [3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3442 34 34, g32p_row03_traceSegment_038_3442_0034, g32p_row03_traceSegment_038_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 3375 135 = [5, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3375 67 68, g32p_row03_traceSegment_038_3375_0067, g32p_row03_traceSegment_038_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 3240 270 = [5, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3240 135 135, g32p_row03_traceSegment_038_3240_0135, g32p_row03_traceSegment_038_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3526 8 9, g32p_row03_traceSegment_038_3526_0008, g32p_row03_traceSegment_038_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3510 16 17, g32p_row03_traceSegment_038_3510_0016, g32p_row03_traceSegment_038_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3543 8 9, g32p_row03_traceSegment_038_3543_0008, g32p_row03_traceSegment_038_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3568 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3560 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3560 8 9, g32p_row03_traceSegment_038_3560_0008, g32p_row03_traceSegment_038_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3543 34 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3543 17 17, g32p_row03_traceSegment_038_3543_0017, g32p_row03_traceSegment_038_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 3510 67 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3510 33 34, g32p_row03_traceSegment_038_3510_0033, g32p_row03_traceSegment_038_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3577 8 9, g32p_row03_traceSegment_038_3577_0008, g32p_row03_traceSegment_038_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3594 8 9, g32p_row03_traceSegment_038_3594_0008, g32p_row03_traceSegment_038_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3577 17 17, g32p_row03_traceSegment_038_3577_0017, g32p_row03_traceSegment_038_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3619 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3611 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3611 8 9, g32p_row03_traceSegment_038_3611_0008, g32p_row03_traceSegment_038_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3628 8 9, g32p_row03_traceSegment_038_3628_0008, g32p_row03_traceSegment_038_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3611 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3611 17 17, g32p_row03_traceSegment_038_3611_0017, g32p_row03_traceSegment_038_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 3577 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3577 34 34, g32p_row03_traceSegment_038_3577_0034, g32p_row03_traceSegment_038_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 3510 135 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3510 67 68, g32p_row03_traceSegment_038_3510_0067, g32p_row03_traceSegment_038_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 3645 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3661 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3669 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3661 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3661 8 9, g32p_row03_traceSegment_038_3661_0008, g32p_row03_traceSegment_038_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 3645 33 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3645 16 17, g32p_row03_traceSegment_038_3645_0016, g32p_row03_traceSegment_038_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3678 8 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3678 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3678 8 9, g32p_row03_traceSegment_038_3678_0008, g32p_row03_traceSegment_038_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3695 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3695 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3695 8 9, g32p_row03_traceSegment_038_3695_0008, g32p_row03_traceSegment_038_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3678 34 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3678 17 17, g32p_row03_traceSegment_038_3678_0017, g32p_row03_traceSegment_038_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 3645 67 = [2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3645 33 34, g32p_row03_traceSegment_038_3645_0033, g32p_row03_traceSegment_038_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3712 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3712 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3712 8 9, g32p_row03_traceSegment_038_3712_0008, g32p_row03_traceSegment_038_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3737 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3729 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3729 8 9, g32p_row03_traceSegment_038_3729_0008, g32p_row03_traceSegment_038_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3712 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3712 17 17, g32p_row03_traceSegment_038_3712_0017, g32p_row03_traceSegment_038_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3746 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3754 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3746 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3746 8 9, g32p_row03_traceSegment_038_3746_0008, g32p_row03_traceSegment_038_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3763 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3763 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3763 8 9, g32p_row03_traceSegment_038_3763_0008, g32p_row03_traceSegment_038_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3746 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3746 17 17, g32p_row03_traceSegment_038_3746_0017, g32p_row03_traceSegment_038_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 3712 68 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3712 34 34, g32p_row03_traceSegment_038_3712_0034, g32p_row03_traceSegment_038_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 3645 135 = [7, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3645 67 68, g32p_row03_traceSegment_038_3645_0067, g32p_row03_traceSegment_038_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 3510 270 = [9, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3510 135 135, g32p_row03_traceSegment_038_3510_0135, g32p_row03_traceSegment_038_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_038 3240 540 = [14, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3240 270 270, g32p_row03_traceSegment_038_3240_0270, g32p_row03_traceSegment_038_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 3780 16 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3796 8 9, g32p_row03_traceSegment_038_3796_0008, g32p_row03_traceSegment_038_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 3780 33 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3780 16 17, g32p_row03_traceSegment_038_3780_0016, g32p_row03_traceSegment_038_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3813 8 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3813 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3813 8 9, g32p_row03_traceSegment_038_3813_0008, g32p_row03_traceSegment_038_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3830 8 9, g32p_row03_traceSegment_038_3830_0008, g32p_row03_traceSegment_038_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3813 34 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3813 17 17, g32p_row03_traceSegment_038_3813_0017, g32p_row03_traceSegment_038_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 3780 67 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3780 33 34, g32p_row03_traceSegment_038_3780_0033, g32p_row03_traceSegment_038_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3847 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3847 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3847 8 9, g32p_row03_traceSegment_038_3847_0008, g32p_row03_traceSegment_038_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3864 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3864 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3864 8 9, g32p_row03_traceSegment_038_3864_0008, g32p_row03_traceSegment_038_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3847 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3847 17 17, g32p_row03_traceSegment_038_3847_0017, g32p_row03_traceSegment_038_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3881 8 9, g32p_row03_traceSegment_038_3881_0008, g32p_row03_traceSegment_038_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3898 8 9, g32p_row03_traceSegment_038_3898_0008, g32p_row03_traceSegment_038_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3881 17 17, g32p_row03_traceSegment_038_3881_0017, g32p_row03_traceSegment_038_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 3847 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3847 34 34, g32p_row03_traceSegment_038_3847_0034, g32p_row03_traceSegment_038_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 3780 135 = [4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3780 67 68, g32p_row03_traceSegment_038_3780_0067, g32p_row03_traceSegment_038_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3939 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3931 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3931 8 9, g32p_row03_traceSegment_038_3931_0008, g32p_row03_traceSegment_038_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 3915 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3915 16 17, g32p_row03_traceSegment_038_3915_0016, g32p_row03_traceSegment_038_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3948 8 9, g32p_row03_traceSegment_038_3948_0008, g32p_row03_traceSegment_038_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3973 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3965 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3965 8 9, g32p_row03_traceSegment_038_3965_0008, g32p_row03_traceSegment_038_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3948 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3948 17 17, g32p_row03_traceSegment_038_3948_0017, g32p_row03_traceSegment_038_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 3915 67 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3915 33 34, g32p_row03_traceSegment_038_3915_0033, g32p_row03_traceSegment_038_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3982 8 9, g32p_row03_traceSegment_038_3982_0008, g32p_row03_traceSegment_038_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4007 9 = [2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 3999 17 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3999 8 9, g32p_row03_traceSegment_038_3999_0008, g32p_row03_traceSegment_038_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 3982 34 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3982 17 17, g32p_row03_traceSegment_038_3982_0017, g32p_row03_traceSegment_038_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4016 8 9, g32p_row03_traceSegment_038_4016_0008, g32p_row03_traceSegment_038_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4033 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4033 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4033 8 9, g32p_row03_traceSegment_038_4033_0008, g32p_row03_traceSegment_038_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 4016 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4016 17 17, g32p_row03_traceSegment_038_4016_0017, g32p_row03_traceSegment_038_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 3982 68 = [4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3982 34 34, g32p_row03_traceSegment_038_3982_0034, g32p_row03_traceSegment_038_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 3915 135 = [6, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3915 67 68, g32p_row03_traceSegment_038_3915_0067, g32p_row03_traceSegment_038_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 3780 270 = [10, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3780 135 135, g32p_row03_traceSegment_038_3780_0135, g32p_row03_traceSegment_038_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 4050 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4074 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4066 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4066 8 9, g32p_row03_traceSegment_038_4066_0008, g32p_row03_traceSegment_038_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 4050 33 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4050 16 17, g32p_row03_traceSegment_038_4050_0016, g32p_row03_traceSegment_038_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4083 8 9, g32p_row03_traceSegment_038_4083_0008, g32p_row03_traceSegment_038_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4100 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4100 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4100 8 9, g32p_row03_traceSegment_038_4100_0008, g32p_row03_traceSegment_038_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 4083 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4083 17 17, g32p_row03_traceSegment_038_4083_0017, g32p_row03_traceSegment_038_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 4050 67 = [1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4050 33 34, g32p_row03_traceSegment_038_4050_0033, g32p_row03_traceSegment_038_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4117 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4117 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4117 8 9, g32p_row03_traceSegment_038_4117_0008, g32p_row03_traceSegment_038_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4134 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4142 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4134 17 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4134 8 9, g32p_row03_traceSegment_038_4134_0008, g32p_row03_traceSegment_038_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 4117 34 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4117 17 17, g32p_row03_traceSegment_038_4117_0017, g32p_row03_traceSegment_038_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4159 9 = [1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4151 17 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4151 8 9, g32p_row03_traceSegment_038_4151_0008, g32p_row03_traceSegment_038_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4176 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4168 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4168 8 9, g32p_row03_traceSegment_038_4168_0008, g32p_row03_traceSegment_038_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 4151 34 = [1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4151 17 17, g32p_row03_traceSegment_038_4151_0017, g32p_row03_traceSegment_038_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 4117 68 = [2, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4117 34 34, g32p_row03_traceSegment_038_4117_0034, g32p_row03_traceSegment_038_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 4050 135 = [3, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4050 67 68, g32p_row03_traceSegment_038_4050_0067, g32p_row03_traceSegment_038_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_038 4185 16 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4201 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4209 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4201 17 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4201 8 9, g32p_row03_traceSegment_038_4201_0008, g32p_row03_traceSegment_038_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_038 4185 33 = [1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4185 16 17, g32p_row03_traceSegment_038_4185_0016, g32p_row03_traceSegment_038_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4218 8 9, g32p_row03_traceSegment_038_4218_0008, g32p_row03_traceSegment_038_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4235 8 9, g32p_row03_traceSegment_038_4235_0008, g32p_row03_traceSegment_038_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4218 17 17, g32p_row03_traceSegment_038_4218_0017, g32p_row03_traceSegment_038_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_038 4185 67 = [1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4185 33 34, g32p_row03_traceSegment_038_4185_0033, g32p_row03_traceSegment_038_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4252 8 9, g32p_row03_traceSegment_038_4252_0008, g32p_row03_traceSegment_038_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4269 8 9, g32p_row03_traceSegment_038_4269_0008, g32p_row03_traceSegment_038_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4252 17 17, g32p_row03_traceSegment_038_4252_0017, g32p_row03_traceSegment_038_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4286 8 9, g32p_row03_traceSegment_038_4286_0008, g32p_row03_traceSegment_038_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_038 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_038 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_038_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_038 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4303 8 9, g32p_row03_traceSegment_038_4303_0008, g32p_row03_traceSegment_038_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_038 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4286 17 17, g32p_row03_traceSegment_038_4286_0017, g32p_row03_traceSegment_038_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_038 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4252 34 34, g32p_row03_traceSegment_038_4252_0034, g32p_row03_traceSegment_038_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_038 4185 135 = [1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4185 67 68, g32p_row03_traceSegment_038_4185_0067, g32p_row03_traceSegment_038_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_038_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_038 4050 270 = [4, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 4050 135 135, g32p_row03_traceSegment_038_4050_0135, g32p_row03_traceSegment_038_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_038 3780 540 = [14, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3780 270 270, g32p_row03_traceSegment_038_3780_0270, g32p_row03_traceSegment_038_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_038_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_038 3240 1080 = [28, 0, 0, 35] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 3240 540 540, g32p_row03_traceSegment_038_3240_0540, g32p_row03_traceSegment_038_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_038_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_038 2160 2160 = [78, 0, 0, 58] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 2160 1080 1080, g32p_row03_traceSegment_038_2160_1080, g32p_row03_traceSegment_038_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_038_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_038 0 4320 = [180, 0, 0, 180] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_038 0 2160 2160, g32p_row03_traceSegment_038_0000_2160, g32p_row03_traceSegment_038_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_038 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 38 = [180, 0, 0, 180] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_038_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_040 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 40 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_040_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 16 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 24 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 16 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 16 8 9, g32p_row03_traceSegment_040_0016_0008, g32p_row03_traceSegment_040_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 0 33 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 0 16 17, g32p_row03_traceSegment_040_0000_0016, g32p_row03_traceSegment_040_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 33 8 9, g32p_row03_traceSegment_040_0033_0008, g32p_row03_traceSegment_040_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 50 8 9, g32p_row03_traceSegment_040_0050_0008, g32p_row03_traceSegment_040_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 33 17 17, g32p_row03_traceSegment_040_0033_0017, g32p_row03_traceSegment_040_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 0 67 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 0 33 34, g32p_row03_traceSegment_040_0000_0033, g32p_row03_traceSegment_040_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 67 8 9, g32p_row03_traceSegment_040_0067_0008, g32p_row03_traceSegment_040_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 84 8 9, g32p_row03_traceSegment_040_0084_0008, g32p_row03_traceSegment_040_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 67 17 17, g32p_row03_traceSegment_040_0067_0017, g32p_row03_traceSegment_040_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 101 8 9, g32p_row03_traceSegment_040_0101_0008, g32p_row03_traceSegment_040_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 118 8 9, g32p_row03_traceSegment_040_0118_0008, g32p_row03_traceSegment_040_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 101 17 17, g32p_row03_traceSegment_040_0101_0017, g32p_row03_traceSegment_040_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 67 34 34, g32p_row03_traceSegment_040_0067_0034, g32p_row03_traceSegment_040_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 0 135 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 0 67 68, g32p_row03_traceSegment_040_0000_0067, g32p_row03_traceSegment_040_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 151 8 9, g32p_row03_traceSegment_040_0151_0008, g32p_row03_traceSegment_040_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 135 16 17, g32p_row03_traceSegment_040_0135_0016, g32p_row03_traceSegment_040_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 168 8 9, g32p_row03_traceSegment_040_0168_0008, g32p_row03_traceSegment_040_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 185 8 9, g32p_row03_traceSegment_040_0185_0008, g32p_row03_traceSegment_040_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 168 17 17, g32p_row03_traceSegment_040_0168_0017, g32p_row03_traceSegment_040_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 135 33 34, g32p_row03_traceSegment_040_0135_0033, g32p_row03_traceSegment_040_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 202 8 9, g32p_row03_traceSegment_040_0202_0008, g32p_row03_traceSegment_040_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 219 8 9, g32p_row03_traceSegment_040_0219_0008, g32p_row03_traceSegment_040_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 202 17 17, g32p_row03_traceSegment_040_0202_0017, g32p_row03_traceSegment_040_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 236 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 236 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 236 8 9, g32p_row03_traceSegment_040_0236_0008, g32p_row03_traceSegment_040_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 253 8 9, g32p_row03_traceSegment_040_0253_0008, g32p_row03_traceSegment_040_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 236 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 236 17 17, g32p_row03_traceSegment_040_0236_0017, g32p_row03_traceSegment_040_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 202 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 202 34 34, g32p_row03_traceSegment_040_0202_0034, g32p_row03_traceSegment_040_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 135 135 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 135 67 68, g32p_row03_traceSegment_040_0135_0067, g32p_row03_traceSegment_040_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 0 270 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 0 135 135, g32p_row03_traceSegment_040_0000_0135, g32p_row03_traceSegment_040_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 270 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 286 8 9, g32p_row03_traceSegment_040_0286_0008, g32p_row03_traceSegment_040_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 270 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 270 16 17, g32p_row03_traceSegment_040_0270_0016, g32p_row03_traceSegment_040_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 303 8 9, g32p_row03_traceSegment_040_0303_0008, g32p_row03_traceSegment_040_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 320 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 320 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 320 8 9, g32p_row03_traceSegment_040_0320_0008, g32p_row03_traceSegment_040_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 303 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 303 17 17, g32p_row03_traceSegment_040_0303_0017, g32p_row03_traceSegment_040_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 270 67 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 270 33 34, g32p_row03_traceSegment_040_0270_0033, g32p_row03_traceSegment_040_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 337 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 337 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 337 8 9, g32p_row03_traceSegment_040_0337_0008, g32p_row03_traceSegment_040_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 354 8 9, g32p_row03_traceSegment_040_0354_0008, g32p_row03_traceSegment_040_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 337 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 337 17 17, g32p_row03_traceSegment_040_0337_0017, g32p_row03_traceSegment_040_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 371 8 9, g32p_row03_traceSegment_040_0371_0008, g32p_row03_traceSegment_040_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 388 8 9, g32p_row03_traceSegment_040_0388_0008, g32p_row03_traceSegment_040_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 371 17 17, g32p_row03_traceSegment_040_0371_0017, g32p_row03_traceSegment_040_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 337 68 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 337 34 34, g32p_row03_traceSegment_040_0337_0034, g32p_row03_traceSegment_040_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 270 135 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 270 67 68, g32p_row03_traceSegment_040_0270_0067, g32p_row03_traceSegment_040_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 421 8 9, g32p_row03_traceSegment_040_0421_0008, g32p_row03_traceSegment_040_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 405 16 17, g32p_row03_traceSegment_040_0405_0016, g32p_row03_traceSegment_040_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 438 8 9, g32p_row03_traceSegment_040_0438_0008, g32p_row03_traceSegment_040_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 455 8 9, g32p_row03_traceSegment_040_0455_0008, g32p_row03_traceSegment_040_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 438 17 17, g32p_row03_traceSegment_040_0438_0017, g32p_row03_traceSegment_040_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 405 33 34, g32p_row03_traceSegment_040_0405_0033, g32p_row03_traceSegment_040_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 472 8 9, g32p_row03_traceSegment_040_0472_0008, g32p_row03_traceSegment_040_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 489 8 9, g32p_row03_traceSegment_040_0489_0008, g32p_row03_traceSegment_040_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 472 17 17, g32p_row03_traceSegment_040_0472_0017, g32p_row03_traceSegment_040_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 506 8 9, g32p_row03_traceSegment_040_0506_0008, g32p_row03_traceSegment_040_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 523 8 9, g32p_row03_traceSegment_040_0523_0008, g32p_row03_traceSegment_040_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 506 17 17, g32p_row03_traceSegment_040_0506_0017, g32p_row03_traceSegment_040_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 472 34 34, g32p_row03_traceSegment_040_0472_0034, g32p_row03_traceSegment_040_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 405 67 68, g32p_row03_traceSegment_040_0405_0067, g32p_row03_traceSegment_040_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 270 270 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 270 135 135, g32p_row03_traceSegment_040_0270_0135, g32p_row03_traceSegment_040_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_040 0 540 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 0 270 270, g32p_row03_traceSegment_040_0000_0270, g32p_row03_traceSegment_040_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 556 8 9, g32p_row03_traceSegment_040_0556_0008, g32p_row03_traceSegment_040_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 540 16 17, g32p_row03_traceSegment_040_0540_0016, g32p_row03_traceSegment_040_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 573 8 9, g32p_row03_traceSegment_040_0573_0008, g32p_row03_traceSegment_040_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 590 8 9, g32p_row03_traceSegment_040_0590_0008, g32p_row03_traceSegment_040_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 573 17 17, g32p_row03_traceSegment_040_0573_0017, g32p_row03_traceSegment_040_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 540 33 34, g32p_row03_traceSegment_040_0540_0033, g32p_row03_traceSegment_040_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 607 8 9, g32p_row03_traceSegment_040_0607_0008, g32p_row03_traceSegment_040_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 624 8 9, g32p_row03_traceSegment_040_0624_0008, g32p_row03_traceSegment_040_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 607 17 17, g32p_row03_traceSegment_040_0607_0017, g32p_row03_traceSegment_040_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 641 8 9, g32p_row03_traceSegment_040_0641_0008, g32p_row03_traceSegment_040_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 658 8 9, g32p_row03_traceSegment_040_0658_0008, g32p_row03_traceSegment_040_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 641 17 17, g32p_row03_traceSegment_040_0641_0017, g32p_row03_traceSegment_040_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 607 34 34, g32p_row03_traceSegment_040_0607_0034, g32p_row03_traceSegment_040_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 540 67 68, g32p_row03_traceSegment_040_0540_0067, g32p_row03_traceSegment_040_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 691 8 9, g32p_row03_traceSegment_040_0691_0008, g32p_row03_traceSegment_040_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 675 16 17, g32p_row03_traceSegment_040_0675_0016, g32p_row03_traceSegment_040_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 708 8 9, g32p_row03_traceSegment_040_0708_0008, g32p_row03_traceSegment_040_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 725 8 9, g32p_row03_traceSegment_040_0725_0008, g32p_row03_traceSegment_040_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 708 17 17, g32p_row03_traceSegment_040_0708_0017, g32p_row03_traceSegment_040_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 675 33 34, g32p_row03_traceSegment_040_0675_0033, g32p_row03_traceSegment_040_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 742 8 9, g32p_row03_traceSegment_040_0742_0008, g32p_row03_traceSegment_040_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 759 8 9, g32p_row03_traceSegment_040_0759_0008, g32p_row03_traceSegment_040_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 742 17 17, g32p_row03_traceSegment_040_0742_0017, g32p_row03_traceSegment_040_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 776 8 9, g32p_row03_traceSegment_040_0776_0008, g32p_row03_traceSegment_040_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 793 8 9, g32p_row03_traceSegment_040_0793_0008, g32p_row03_traceSegment_040_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 776 17 17, g32p_row03_traceSegment_040_0776_0017, g32p_row03_traceSegment_040_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 742 34 34, g32p_row03_traceSegment_040_0742_0034, g32p_row03_traceSegment_040_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 675 67 68, g32p_row03_traceSegment_040_0675_0067, g32p_row03_traceSegment_040_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 540 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 540 135 135, g32p_row03_traceSegment_040_0540_0135, g32p_row03_traceSegment_040_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 826 8 9, g32p_row03_traceSegment_040_0826_0008, g32p_row03_traceSegment_040_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 810 16 17, g32p_row03_traceSegment_040_0810_0016, g32p_row03_traceSegment_040_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 843 8 9, g32p_row03_traceSegment_040_0843_0008, g32p_row03_traceSegment_040_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 860 8 9, g32p_row03_traceSegment_040_0860_0008, g32p_row03_traceSegment_040_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 843 17 17, g32p_row03_traceSegment_040_0843_0017, g32p_row03_traceSegment_040_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 810 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 810 33 34, g32p_row03_traceSegment_040_0810_0033, g32p_row03_traceSegment_040_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 877 8 9, g32p_row03_traceSegment_040_0877_0008, g32p_row03_traceSegment_040_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 894 8 9, g32p_row03_traceSegment_040_0894_0008, g32p_row03_traceSegment_040_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 877 17 17, g32p_row03_traceSegment_040_0877_0017, g32p_row03_traceSegment_040_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 911 8 9, g32p_row03_traceSegment_040_0911_0008, g32p_row03_traceSegment_040_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 928 8 9, g32p_row03_traceSegment_040_0928_0008, g32p_row03_traceSegment_040_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 911 17 17, g32p_row03_traceSegment_040_0911_0017, g32p_row03_traceSegment_040_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 877 34 34, g32p_row03_traceSegment_040_0877_0034, g32p_row03_traceSegment_040_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 810 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 810 67 68, g32p_row03_traceSegment_040_0810_0067, g32p_row03_traceSegment_040_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 961 8 9, g32p_row03_traceSegment_040_0961_0008, g32p_row03_traceSegment_040_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 945 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 945 16 17, g32p_row03_traceSegment_040_0945_0016, g32p_row03_traceSegment_040_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 978 8 9, g32p_row03_traceSegment_040_0978_0008, g32p_row03_traceSegment_040_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 995 8 9, g32p_row03_traceSegment_040_0995_0008, g32p_row03_traceSegment_040_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 978 17 17, g32p_row03_traceSegment_040_0978_0017, g32p_row03_traceSegment_040_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 945 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 945 33 34, g32p_row03_traceSegment_040_0945_0033, g32p_row03_traceSegment_040_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1012 8 9, g32p_row03_traceSegment_040_1012_0008, g32p_row03_traceSegment_040_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1029 8 9, g32p_row03_traceSegment_040_1029_0008, g32p_row03_traceSegment_040_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1012 17 17, g32p_row03_traceSegment_040_1012_0017, g32p_row03_traceSegment_040_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1046 8 9, g32p_row03_traceSegment_040_1046_0008, g32p_row03_traceSegment_040_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1063 8 9, g32p_row03_traceSegment_040_1063_0008, g32p_row03_traceSegment_040_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1046 17 17, g32p_row03_traceSegment_040_1046_0017, g32p_row03_traceSegment_040_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1012 34 34, g32p_row03_traceSegment_040_1012_0034, g32p_row03_traceSegment_040_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 945 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 945 67 68, g32p_row03_traceSegment_040_0945_0067, g32p_row03_traceSegment_040_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 810 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 810 135 135, g32p_row03_traceSegment_040_0810_0135, g32p_row03_traceSegment_040_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_040 540 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 540 270 270, g32p_row03_traceSegment_040_0540_0270, g32p_row03_traceSegment_040_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_040 0 1080 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 0 540 540, g32p_row03_traceSegment_040_0000_0540, g32p_row03_traceSegment_040_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1096 8 9, g32p_row03_traceSegment_040_1096_0008, g32p_row03_traceSegment_040_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1080 16 17, g32p_row03_traceSegment_040_1080_0016, g32p_row03_traceSegment_040_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1113 8 9, g32p_row03_traceSegment_040_1113_0008, g32p_row03_traceSegment_040_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1130 8 9, g32p_row03_traceSegment_040_1130_0008, g32p_row03_traceSegment_040_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1113 17 17, g32p_row03_traceSegment_040_1113_0017, g32p_row03_traceSegment_040_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1080 33 34, g32p_row03_traceSegment_040_1080_0033, g32p_row03_traceSegment_040_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1147 8 9, g32p_row03_traceSegment_040_1147_0008, g32p_row03_traceSegment_040_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1164 8 9, g32p_row03_traceSegment_040_1164_0008, g32p_row03_traceSegment_040_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1147 17 17, g32p_row03_traceSegment_040_1147_0017, g32p_row03_traceSegment_040_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1181 8 9, g32p_row03_traceSegment_040_1181_0008, g32p_row03_traceSegment_040_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1198 8 9, g32p_row03_traceSegment_040_1198_0008, g32p_row03_traceSegment_040_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1181 17 17, g32p_row03_traceSegment_040_1181_0017, g32p_row03_traceSegment_040_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1147 34 34, g32p_row03_traceSegment_040_1147_0034, g32p_row03_traceSegment_040_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1080 67 68, g32p_row03_traceSegment_040_1080_0067, g32p_row03_traceSegment_040_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1231 8 9, g32p_row03_traceSegment_040_1231_0008, g32p_row03_traceSegment_040_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1215 16 17, g32p_row03_traceSegment_040_1215_0016, g32p_row03_traceSegment_040_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1248 8 9, g32p_row03_traceSegment_040_1248_0008, g32p_row03_traceSegment_040_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1265 8 9, g32p_row03_traceSegment_040_1265_0008, g32p_row03_traceSegment_040_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1248 17 17, g32p_row03_traceSegment_040_1248_0017, g32p_row03_traceSegment_040_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1215 33 34, g32p_row03_traceSegment_040_1215_0033, g32p_row03_traceSegment_040_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1282 8 9, g32p_row03_traceSegment_040_1282_0008, g32p_row03_traceSegment_040_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1299 8 9, g32p_row03_traceSegment_040_1299_0008, g32p_row03_traceSegment_040_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1282 17 17, g32p_row03_traceSegment_040_1282_0017, g32p_row03_traceSegment_040_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1316 8 9, g32p_row03_traceSegment_040_1316_0008, g32p_row03_traceSegment_040_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1333 8 9, g32p_row03_traceSegment_040_1333_0008, g32p_row03_traceSegment_040_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1316 17 17, g32p_row03_traceSegment_040_1316_0017, g32p_row03_traceSegment_040_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1282 34 34, g32p_row03_traceSegment_040_1282_0034, g32p_row03_traceSegment_040_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1215 67 68, g32p_row03_traceSegment_040_1215_0067, g32p_row03_traceSegment_040_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 1080 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1080 135 135, g32p_row03_traceSegment_040_1080_0135, g32p_row03_traceSegment_040_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 1350 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1366 8 9, g32p_row03_traceSegment_040_1366_0008, g32p_row03_traceSegment_040_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 1350 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1350 16 17, g32p_row03_traceSegment_040_1350_0016, g32p_row03_traceSegment_040_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1383 8 9, g32p_row03_traceSegment_040_1383_0008, g32p_row03_traceSegment_040_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1400 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1400 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1400 8 9, g32p_row03_traceSegment_040_1400_0008, g32p_row03_traceSegment_040_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1383 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1383 17 17, g32p_row03_traceSegment_040_1383_0017, g32p_row03_traceSegment_040_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 1350 67 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1350 33 34, g32p_row03_traceSegment_040_1350_0033, g32p_row03_traceSegment_040_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1417 8 9, g32p_row03_traceSegment_040_1417_0008, g32p_row03_traceSegment_040_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1442 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1434 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1434 8 9, g32p_row03_traceSegment_040_1434_0008, g32p_row03_traceSegment_040_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1417 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1417 17 17, g32p_row03_traceSegment_040_1417_0017, g32p_row03_traceSegment_040_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1451 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1451 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1451 8 9, g32p_row03_traceSegment_040_1451_0008, g32p_row03_traceSegment_040_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1468 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1476 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1468 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1468 8 9, g32p_row03_traceSegment_040_1468_0008, g32p_row03_traceSegment_040_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1451 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1451 17 17, g32p_row03_traceSegment_040_1451_0017, g32p_row03_traceSegment_040_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 1417 68 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1417 34 34, g32p_row03_traceSegment_040_1417_0034, g32p_row03_traceSegment_040_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 1350 135 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1350 67 68, g32p_row03_traceSegment_040_1350_0067, g32p_row03_traceSegment_040_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 1485 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1509 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1501 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1501 8 9, g32p_row03_traceSegment_040_1501_0008, g32p_row03_traceSegment_040_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 1485 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1485 16 17, g32p_row03_traceSegment_040_1485_0016, g32p_row03_traceSegment_040_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1526 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1518 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1518 8 9, g32p_row03_traceSegment_040_1518_0008, g32p_row03_traceSegment_040_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1535 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1535 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1535 8 9, g32p_row03_traceSegment_040_1535_0008, g32p_row03_traceSegment_040_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1518 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1518 17 17, g32p_row03_traceSegment_040_1518_0017, g32p_row03_traceSegment_040_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 1485 67 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1485 33 34, g32p_row03_traceSegment_040_1485_0033, g32p_row03_traceSegment_040_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1552 8 9, g32p_row03_traceSegment_040_1552_0008, g32p_row03_traceSegment_040_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1569 8 9, g32p_row03_traceSegment_040_1569_0008, g32p_row03_traceSegment_040_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1552 17 17, g32p_row03_traceSegment_040_1552_0017, g32p_row03_traceSegment_040_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1586 8 9, g32p_row03_traceSegment_040_1586_0008, g32p_row03_traceSegment_040_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1603 8 9, g32p_row03_traceSegment_040_1603_0008, g32p_row03_traceSegment_040_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1586 17 17, g32p_row03_traceSegment_040_1586_0017, g32p_row03_traceSegment_040_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1552 34 34, g32p_row03_traceSegment_040_1552_0034, g32p_row03_traceSegment_040_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 1485 135 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1485 67 68, g32p_row03_traceSegment_040_1485_0067, g32p_row03_traceSegment_040_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 1350 270 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1350 135 135, g32p_row03_traceSegment_040_1350_0135, g32p_row03_traceSegment_040_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_040 1080 540 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1080 270 270, g32p_row03_traceSegment_040_1080_0270, g32p_row03_traceSegment_040_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 1620 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1636 8 9, g32p_row03_traceSegment_040_1636_0008, g32p_row03_traceSegment_040_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 1620 33 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1620 16 17, g32p_row03_traceSegment_040_1620_0016, g32p_row03_traceSegment_040_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1653 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1661 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1653 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1653 8 9, g32p_row03_traceSegment_040_1653_0008, g32p_row03_traceSegment_040_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1678 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1670 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1670 8 9, g32p_row03_traceSegment_040_1670_0008, g32p_row03_traceSegment_040_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1653 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1653 17 17, g32p_row03_traceSegment_040_1653_0017, g32p_row03_traceSegment_040_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 1620 67 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1620 33 34, g32p_row03_traceSegment_040_1620_0033, g32p_row03_traceSegment_040_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1687 8 9, g32p_row03_traceSegment_040_1687_0008, g32p_row03_traceSegment_040_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1704 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1704 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1704 8 9, g32p_row03_traceSegment_040_1704_0008, g32p_row03_traceSegment_040_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1687 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1687 17 17, g32p_row03_traceSegment_040_1687_0017, g32p_row03_traceSegment_040_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1721 8 9, g32p_row03_traceSegment_040_1721_0008, g32p_row03_traceSegment_040_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1738 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1738 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1738 8 9, g32p_row03_traceSegment_040_1738_0008, g32p_row03_traceSegment_040_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1721 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1721 17 17, g32p_row03_traceSegment_040_1721_0017, g32p_row03_traceSegment_040_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 1687 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1687 34 34, g32p_row03_traceSegment_040_1687_0034, g32p_row03_traceSegment_040_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 1620 135 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1620 67 68, g32p_row03_traceSegment_040_1620_0067, g32p_row03_traceSegment_040_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 1755 16 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1771 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1779 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1771 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1771 8 9, g32p_row03_traceSegment_040_1771_0008, g32p_row03_traceSegment_040_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 1755 33 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1755 16 17, g32p_row03_traceSegment_040_1755_0016, g32p_row03_traceSegment_040_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1788 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1788 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1788 8 9, g32p_row03_traceSegment_040_1788_0008, g32p_row03_traceSegment_040_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1805 8 9, g32p_row03_traceSegment_040_1805_0008, g32p_row03_traceSegment_040_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1788 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1788 17 17, g32p_row03_traceSegment_040_1788_0017, g32p_row03_traceSegment_040_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 1755 67 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1755 33 34, g32p_row03_traceSegment_040_1755_0033, g32p_row03_traceSegment_040_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1822 8 9, g32p_row03_traceSegment_040_1822_0008, g32p_row03_traceSegment_040_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1839 8 9, g32p_row03_traceSegment_040_1839_0008, g32p_row03_traceSegment_040_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1822 17 17, g32p_row03_traceSegment_040_1822_0017, g32p_row03_traceSegment_040_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1856 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1856 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1856 8 9, g32p_row03_traceSegment_040_1856_0008, g32p_row03_traceSegment_040_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1873 8 9, g32p_row03_traceSegment_040_1873_0008, g32p_row03_traceSegment_040_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1856 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1856 17 17, g32p_row03_traceSegment_040_1856_0017, g32p_row03_traceSegment_040_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 1822 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1822 34 34, g32p_row03_traceSegment_040_1822_0034, g32p_row03_traceSegment_040_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 1755 135 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1755 67 68, g32p_row03_traceSegment_040_1755_0067, g32p_row03_traceSegment_040_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 1620 270 = [0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1620 135 135, g32p_row03_traceSegment_040_1620_0135, g32p_row03_traceSegment_040_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 1890 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1906 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1914 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1906 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1906 8 9, g32p_row03_traceSegment_040_1906_0008, g32p_row03_traceSegment_040_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 1890 33 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1890 16 17, g32p_row03_traceSegment_040_1890_0016, g32p_row03_traceSegment_040_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1923 8 9, g32p_row03_traceSegment_040_1923_0008, g32p_row03_traceSegment_040_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1948 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1940 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1940 8 9, g32p_row03_traceSegment_040_1940_0008, g32p_row03_traceSegment_040_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1923 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1923 17 17, g32p_row03_traceSegment_040_1923_0017, g32p_row03_traceSegment_040_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 1890 67 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1890 33 34, g32p_row03_traceSegment_040_1890_0033, g32p_row03_traceSegment_040_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1965 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1957 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1957 8 9, g32p_row03_traceSegment_040_1957_0008, g32p_row03_traceSegment_040_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1974 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1974 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1974 8 9, g32p_row03_traceSegment_040_1974_0008, g32p_row03_traceSegment_040_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1957 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1957 17 17, g32p_row03_traceSegment_040_1957_0017, g32p_row03_traceSegment_040_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 1991 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 1991 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1991 8 9, g32p_row03_traceSegment_040_1991_0008, g32p_row03_traceSegment_040_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2008 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2016 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2008 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2008 8 9, g32p_row03_traceSegment_040_2008_0008, g32p_row03_traceSegment_040_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 1991 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1991 17 17, g32p_row03_traceSegment_040_1991_0017, g32p_row03_traceSegment_040_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 1957 68 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1957 34 34, g32p_row03_traceSegment_040_1957_0034, g32p_row03_traceSegment_040_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 1890 135 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1890 67 68, g32p_row03_traceSegment_040_1890_0067, g32p_row03_traceSegment_040_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 2025 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2049 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2041 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2041 8 9, g32p_row03_traceSegment_040_2041_0008, g32p_row03_traceSegment_040_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 2025 33 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2025 16 17, g32p_row03_traceSegment_040_2025_0016, g32p_row03_traceSegment_040_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2058 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2058 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2058 8 9, g32p_row03_traceSegment_040_2058_0008, g32p_row03_traceSegment_040_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2075 8 9, g32p_row03_traceSegment_040_2075_0008, g32p_row03_traceSegment_040_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2058 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2058 17 17, g32p_row03_traceSegment_040_2058_0017, g32p_row03_traceSegment_040_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 2025 67 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2025 33 34, g32p_row03_traceSegment_040_2025_0033, g32p_row03_traceSegment_040_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2100 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2092 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2092 8 9, g32p_row03_traceSegment_040_2092_0008, g32p_row03_traceSegment_040_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2117 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2109 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2109 8 9, g32p_row03_traceSegment_040_2109_0008, g32p_row03_traceSegment_040_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2092 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2092 17 17, g32p_row03_traceSegment_040_2092_0017, g32p_row03_traceSegment_040_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2126 8 9, g32p_row03_traceSegment_040_2126_0008, g32p_row03_traceSegment_040_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2143 8 9, g32p_row03_traceSegment_040_2143_0008, g32p_row03_traceSegment_040_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2126 17 17, g32p_row03_traceSegment_040_2126_0017, g32p_row03_traceSegment_040_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 2092 68 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2092 34 34, g32p_row03_traceSegment_040_2092_0034, g32p_row03_traceSegment_040_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 2025 135 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2025 67 68, g32p_row03_traceSegment_040_2025_0067, g32p_row03_traceSegment_040_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 1890 270 = [0, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1890 135 135, g32p_row03_traceSegment_040_1890_0135, g32p_row03_traceSegment_040_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_040 1620 540 = [0, 0, 0, 35] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1620 270 270, g32p_row03_traceSegment_040_1620_0270, g32p_row03_traceSegment_040_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_040_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_040 1080 1080 = [0, 0, 0, 47] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 1080 540 540, g32p_row03_traceSegment_040_1080_0540, g32p_row03_traceSegment_040_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_040 0 2160 = [0, 0, 0, 57] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 0 1080 1080, g32p_row03_traceSegment_040_0000_1080, g32p_row03_traceSegment_040_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2176 8 9, g32p_row03_traceSegment_040_2176_0008, g32p_row03_traceSegment_040_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2160 16 17, g32p_row03_traceSegment_040_2160_0016, g32p_row03_traceSegment_040_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2193 8 9, g32p_row03_traceSegment_040_2193_0008, g32p_row03_traceSegment_040_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2210 8 9, g32p_row03_traceSegment_040_2210_0008, g32p_row03_traceSegment_040_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2193 17 17, g32p_row03_traceSegment_040_2193_0017, g32p_row03_traceSegment_040_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 2160 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2160 33 34, g32p_row03_traceSegment_040_2160_0033, g32p_row03_traceSegment_040_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2227 8 9, g32p_row03_traceSegment_040_2227_0008, g32p_row03_traceSegment_040_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2244 8 9, g32p_row03_traceSegment_040_2244_0008, g32p_row03_traceSegment_040_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2227 17 17, g32p_row03_traceSegment_040_2227_0017, g32p_row03_traceSegment_040_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2261 8 9, g32p_row03_traceSegment_040_2261_0008, g32p_row03_traceSegment_040_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2278 8 9, g32p_row03_traceSegment_040_2278_0008, g32p_row03_traceSegment_040_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2261 17 17, g32p_row03_traceSegment_040_2261_0017, g32p_row03_traceSegment_040_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2227 34 34, g32p_row03_traceSegment_040_2227_0034, g32p_row03_traceSegment_040_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 2160 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2160 67 68, g32p_row03_traceSegment_040_2160_0067, g32p_row03_traceSegment_040_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2311 8 9, g32p_row03_traceSegment_040_2311_0008, g32p_row03_traceSegment_040_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2295 16 17, g32p_row03_traceSegment_040_2295_0016, g32p_row03_traceSegment_040_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2328 8 9, g32p_row03_traceSegment_040_2328_0008, g32p_row03_traceSegment_040_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2345 8 9, g32p_row03_traceSegment_040_2345_0008, g32p_row03_traceSegment_040_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2328 17 17, g32p_row03_traceSegment_040_2328_0017, g32p_row03_traceSegment_040_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 2295 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2295 33 34, g32p_row03_traceSegment_040_2295_0033, g32p_row03_traceSegment_040_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2362 8 9, g32p_row03_traceSegment_040_2362_0008, g32p_row03_traceSegment_040_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2379 8 9, g32p_row03_traceSegment_040_2379_0008, g32p_row03_traceSegment_040_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2362 17 17, g32p_row03_traceSegment_040_2362_0017, g32p_row03_traceSegment_040_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2396 8 9, g32p_row03_traceSegment_040_2396_0008, g32p_row03_traceSegment_040_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2413 8 9, g32p_row03_traceSegment_040_2413_0008, g32p_row03_traceSegment_040_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2396 17 17, g32p_row03_traceSegment_040_2396_0017, g32p_row03_traceSegment_040_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2362 34 34, g32p_row03_traceSegment_040_2362_0034, g32p_row03_traceSegment_040_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 2295 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2295 67 68, g32p_row03_traceSegment_040_2295_0067, g32p_row03_traceSegment_040_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 2160 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2160 135 135, g32p_row03_traceSegment_040_2160_0135, g32p_row03_traceSegment_040_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 2430 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2446 8 9, g32p_row03_traceSegment_040_2446_0008, g32p_row03_traceSegment_040_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 2430 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2430 16 17, g32p_row03_traceSegment_040_2430_0016, g32p_row03_traceSegment_040_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2463 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2463 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2463 8 9, g32p_row03_traceSegment_040_2463_0008, g32p_row03_traceSegment_040_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2480 8 9, g32p_row03_traceSegment_040_2480_0008, g32p_row03_traceSegment_040_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2463 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2463 17 17, g32p_row03_traceSegment_040_2463_0017, g32p_row03_traceSegment_040_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 2430 67 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2430 33 34, g32p_row03_traceSegment_040_2430_0033, g32p_row03_traceSegment_040_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2497 8 9, g32p_row03_traceSegment_040_2497_0008, g32p_row03_traceSegment_040_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2514 8 9, g32p_row03_traceSegment_040_2514_0008, g32p_row03_traceSegment_040_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2497 17 17, g32p_row03_traceSegment_040_2497_0017, g32p_row03_traceSegment_040_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2531 8 9, g32p_row03_traceSegment_040_2531_0008, g32p_row03_traceSegment_040_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2548 8 9, g32p_row03_traceSegment_040_2548_0008, g32p_row03_traceSegment_040_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2531 17 17, g32p_row03_traceSegment_040_2531_0017, g32p_row03_traceSegment_040_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2497 34 34, g32p_row03_traceSegment_040_2497_0034, g32p_row03_traceSegment_040_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 2430 135 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2430 67 68, g32p_row03_traceSegment_040_2430_0067, g32p_row03_traceSegment_040_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2581 8 9, g32p_row03_traceSegment_040_2581_0008, g32p_row03_traceSegment_040_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2565 16 17, g32p_row03_traceSegment_040_2565_0016, g32p_row03_traceSegment_040_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2598 8 9, g32p_row03_traceSegment_040_2598_0008, g32p_row03_traceSegment_040_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2615 8 9, g32p_row03_traceSegment_040_2615_0008, g32p_row03_traceSegment_040_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2598 17 17, g32p_row03_traceSegment_040_2598_0017, g32p_row03_traceSegment_040_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 2565 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2565 33 34, g32p_row03_traceSegment_040_2565_0033, g32p_row03_traceSegment_040_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2632 8 9, g32p_row03_traceSegment_040_2632_0008, g32p_row03_traceSegment_040_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2649 8 9, g32p_row03_traceSegment_040_2649_0008, g32p_row03_traceSegment_040_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2632 17 17, g32p_row03_traceSegment_040_2632_0017, g32p_row03_traceSegment_040_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2666 8 9, g32p_row03_traceSegment_040_2666_0008, g32p_row03_traceSegment_040_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2683 8 9, g32p_row03_traceSegment_040_2683_0008, g32p_row03_traceSegment_040_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2666 17 17, g32p_row03_traceSegment_040_2666_0017, g32p_row03_traceSegment_040_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2632 34 34, g32p_row03_traceSegment_040_2632_0034, g32p_row03_traceSegment_040_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 2565 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2565 67 68, g32p_row03_traceSegment_040_2565_0067, g32p_row03_traceSegment_040_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 2430 270 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2430 135 135, g32p_row03_traceSegment_040_2430_0135, g32p_row03_traceSegment_040_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_040 2160 540 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2160 270 270, g32p_row03_traceSegment_040_2160_0270, g32p_row03_traceSegment_040_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2716 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2716 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2716 8 9, g32p_row03_traceSegment_040_2716_0008, g32p_row03_traceSegment_040_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 2700 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2700 16 17, g32p_row03_traceSegment_040_2700_0016, g32p_row03_traceSegment_040_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2733 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2733 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2733 8 9, g32p_row03_traceSegment_040_2733_0008, g32p_row03_traceSegment_040_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2750 8 9, g32p_row03_traceSegment_040_2750_0008, g32p_row03_traceSegment_040_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2733 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2733 17 17, g32p_row03_traceSegment_040_2733_0017, g32p_row03_traceSegment_040_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 2700 67 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2700 33 34, g32p_row03_traceSegment_040_2700_0033, g32p_row03_traceSegment_040_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2767 8 9, g32p_row03_traceSegment_040_2767_0008, g32p_row03_traceSegment_040_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2784 8 9, g32p_row03_traceSegment_040_2784_0008, g32p_row03_traceSegment_040_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2767 17 17, g32p_row03_traceSegment_040_2767_0017, g32p_row03_traceSegment_040_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2801 8 9, g32p_row03_traceSegment_040_2801_0008, g32p_row03_traceSegment_040_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2818 8 9, g32p_row03_traceSegment_040_2818_0008, g32p_row03_traceSegment_040_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2801 17 17, g32p_row03_traceSegment_040_2801_0017, g32p_row03_traceSegment_040_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2767 34 34, g32p_row03_traceSegment_040_2767_0034, g32p_row03_traceSegment_040_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 2700 135 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2700 67 68, g32p_row03_traceSegment_040_2700_0067, g32p_row03_traceSegment_040_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2851 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2851 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2851 8 9, g32p_row03_traceSegment_040_2851_0008, g32p_row03_traceSegment_040_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 2835 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2835 16 17, g32p_row03_traceSegment_040_2835_0016, g32p_row03_traceSegment_040_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2868 8 9, g32p_row03_traceSegment_040_2868_0008, g32p_row03_traceSegment_040_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2885 8 9, g32p_row03_traceSegment_040_2885_0008, g32p_row03_traceSegment_040_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2868 17 17, g32p_row03_traceSegment_040_2868_0017, g32p_row03_traceSegment_040_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 2835 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2835 33 34, g32p_row03_traceSegment_040_2835_0033, g32p_row03_traceSegment_040_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2910 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2902 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2902 8 9, g32p_row03_traceSegment_040_2902_0008, g32p_row03_traceSegment_040_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2919 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2919 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2919 8 9, g32p_row03_traceSegment_040_2919_0008, g32p_row03_traceSegment_040_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2902 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2902 17 17, g32p_row03_traceSegment_040_2902_0017, g32p_row03_traceSegment_040_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2936 8 9, g32p_row03_traceSegment_040_2936_0008, g32p_row03_traceSegment_040_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2953 8 9, g32p_row03_traceSegment_040_2953_0008, g32p_row03_traceSegment_040_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2936 17 17, g32p_row03_traceSegment_040_2936_0017, g32p_row03_traceSegment_040_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 2902 68 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2902 34 34, g32p_row03_traceSegment_040_2902_0034, g32p_row03_traceSegment_040_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 2835 135 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2835 67 68, g32p_row03_traceSegment_040_2835_0067, g32p_row03_traceSegment_040_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 2700 270 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2700 135 135, g32p_row03_traceSegment_040_2700_0135, g32p_row03_traceSegment_040_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2986 8 9, g32p_row03_traceSegment_040_2986_0008, g32p_row03_traceSegment_040_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2970 16 17, g32p_row03_traceSegment_040_2970_0016, g32p_row03_traceSegment_040_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3003 8 9, g32p_row03_traceSegment_040_3003_0008, g32p_row03_traceSegment_040_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3020 8 9, g32p_row03_traceSegment_040_3020_0008, g32p_row03_traceSegment_040_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3003 17 17, g32p_row03_traceSegment_040_3003_0017, g32p_row03_traceSegment_040_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2970 33 34, g32p_row03_traceSegment_040_2970_0033, g32p_row03_traceSegment_040_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3037 8 9, g32p_row03_traceSegment_040_3037_0008, g32p_row03_traceSegment_040_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3054 8 9, g32p_row03_traceSegment_040_3054_0008, g32p_row03_traceSegment_040_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3037 17 17, g32p_row03_traceSegment_040_3037_0017, g32p_row03_traceSegment_040_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3079 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3071 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3071 8 9, g32p_row03_traceSegment_040_3071_0008, g32p_row03_traceSegment_040_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3088 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3096 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3088 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3088 8 9, g32p_row03_traceSegment_040_3088_0008, g32p_row03_traceSegment_040_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3071 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3071 17 17, g32p_row03_traceSegment_040_3071_0017, g32p_row03_traceSegment_040_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 3037 68 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3037 34 34, g32p_row03_traceSegment_040_3037_0034, g32p_row03_traceSegment_040_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 2970 135 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2970 67 68, g32p_row03_traceSegment_040_2970_0067, g32p_row03_traceSegment_040_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 3105 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3129 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3121 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3121 8 9, g32p_row03_traceSegment_040_3121_0008, g32p_row03_traceSegment_040_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 3105 33 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3105 16 17, g32p_row03_traceSegment_040_3105_0016, g32p_row03_traceSegment_040_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3138 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3146 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3138 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3138 8 9, g32p_row03_traceSegment_040_3138_0008, g32p_row03_traceSegment_040_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3163 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3155 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3155 8 9, g32p_row03_traceSegment_040_3155_0008, g32p_row03_traceSegment_040_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3138 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3138 17 17, g32p_row03_traceSegment_040_3138_0017, g32p_row03_traceSegment_040_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 3105 67 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3105 33 34, g32p_row03_traceSegment_040_3105_0033, g32p_row03_traceSegment_040_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3172 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3172 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3172 8 9, g32p_row03_traceSegment_040_3172_0008, g32p_row03_traceSegment_040_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3189 8 9, g32p_row03_traceSegment_040_3189_0008, g32p_row03_traceSegment_040_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3172 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3172 17 17, g32p_row03_traceSegment_040_3172_0017, g32p_row03_traceSegment_040_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3214 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3206 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3206 8 9, g32p_row03_traceSegment_040_3206_0008, g32p_row03_traceSegment_040_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3231 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3223 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3223 8 9, g32p_row03_traceSegment_040_3223_0008, g32p_row03_traceSegment_040_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3206 34 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3206 17 17, g32p_row03_traceSegment_040_3206_0017, g32p_row03_traceSegment_040_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 3172 68 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3172 34 34, g32p_row03_traceSegment_040_3172_0034, g32p_row03_traceSegment_040_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 3105 135 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3105 67 68, g32p_row03_traceSegment_040_3105_0067, g32p_row03_traceSegment_040_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 2970 270 = [0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2970 135 135, g32p_row03_traceSegment_040_2970_0135, g32p_row03_traceSegment_040_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_040 2700 540 = [0, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2700 270 270, g32p_row03_traceSegment_040_2700_0270, g32p_row03_traceSegment_040_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_040 2160 1080 = [0, 0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2160 540 540, g32p_row03_traceSegment_040_2160_0540, g32p_row03_traceSegment_040_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 3240 16 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3256 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3256 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3256 8 9, g32p_row03_traceSegment_040_3256_0008, g32p_row03_traceSegment_040_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 3240 33 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3240 16 17, g32p_row03_traceSegment_040_3240_0016, g32p_row03_traceSegment_040_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3273 8 9, g32p_row03_traceSegment_040_3273_0008, g32p_row03_traceSegment_040_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3290 8 9, g32p_row03_traceSegment_040_3290_0008, g32p_row03_traceSegment_040_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3273 17 17, g32p_row03_traceSegment_040_3273_0017, g32p_row03_traceSegment_040_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 3240 67 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3240 33 34, g32p_row03_traceSegment_040_3240_0033, g32p_row03_traceSegment_040_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3307 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3315 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3307 17 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3307 8 9, g32p_row03_traceSegment_040_3307_0008, g32p_row03_traceSegment_040_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3324 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3324 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3324 8 9, g32p_row03_traceSegment_040_3324_0008, g32p_row03_traceSegment_040_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3307 34 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3307 17 17, g32p_row03_traceSegment_040_3307_0017, g32p_row03_traceSegment_040_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3341 8 9, g32p_row03_traceSegment_040_3341_0008, g32p_row03_traceSegment_040_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3366 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3358 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3358 8 9, g32p_row03_traceSegment_040_3358_0008, g32p_row03_traceSegment_040_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3341 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3341 17 17, g32p_row03_traceSegment_040_3341_0017, g32p_row03_traceSegment_040_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 3307 68 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3307 34 34, g32p_row03_traceSegment_040_3307_0034, g32p_row03_traceSegment_040_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 3240 135 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3240 67 68, g32p_row03_traceSegment_040_3240_0067, g32p_row03_traceSegment_040_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3391 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3399 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3391 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3391 8 9, g32p_row03_traceSegment_040_3391_0008, g32p_row03_traceSegment_040_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 3375 33 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3375 16 17, g32p_row03_traceSegment_040_3375_0016, g32p_row03_traceSegment_040_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3408 8 9, g32p_row03_traceSegment_040_3408_0008, g32p_row03_traceSegment_040_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3433 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3425 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3425 8 9, g32p_row03_traceSegment_040_3425_0008, g32p_row03_traceSegment_040_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3408 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3408 17 17, g32p_row03_traceSegment_040_3408_0017, g32p_row03_traceSegment_040_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 3375 67 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3375 33 34, g32p_row03_traceSegment_040_3375_0033, g32p_row03_traceSegment_040_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3442 8 9, g32p_row03_traceSegment_040_3442_0008, g32p_row03_traceSegment_040_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3459 8 9, g32p_row03_traceSegment_040_3459_0008, g32p_row03_traceSegment_040_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3442 17 17, g32p_row03_traceSegment_040_3442_0017, g32p_row03_traceSegment_040_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3476 8 9, g32p_row03_traceSegment_040_3476_0008, g32p_row03_traceSegment_040_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3493 8 9, g32p_row03_traceSegment_040_3493_0008, g32p_row03_traceSegment_040_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3476 17 17, g32p_row03_traceSegment_040_3476_0017, g32p_row03_traceSegment_040_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 3442 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3442 34 34, g32p_row03_traceSegment_040_3442_0034, g32p_row03_traceSegment_040_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 3375 135 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3375 67 68, g32p_row03_traceSegment_040_3375_0067, g32p_row03_traceSegment_040_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 3240 270 = [0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3240 135 135, g32p_row03_traceSegment_040_3240_0135, g32p_row03_traceSegment_040_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 3510 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3534 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3526 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3526 8 9, g32p_row03_traceSegment_040_3526_0008, g32p_row03_traceSegment_040_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 3510 33 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3510 16 17, g32p_row03_traceSegment_040_3510_0016, g32p_row03_traceSegment_040_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3551 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3543 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3543 8 9, g32p_row03_traceSegment_040_3543_0008, g32p_row03_traceSegment_040_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3560 8 9, g32p_row03_traceSegment_040_3560_0008, g32p_row03_traceSegment_040_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3543 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3543 17 17, g32p_row03_traceSegment_040_3543_0017, g32p_row03_traceSegment_040_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 3510 67 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3510 33 34, g32p_row03_traceSegment_040_3510_0033, g32p_row03_traceSegment_040_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3577 8 9, g32p_row03_traceSegment_040_3577_0008, g32p_row03_traceSegment_040_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3594 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3602 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3594 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3594 8 9, g32p_row03_traceSegment_040_3594_0008, g32p_row03_traceSegment_040_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3577 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3577 17 17, g32p_row03_traceSegment_040_3577_0017, g32p_row03_traceSegment_040_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3611 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3611 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3611 8 9, g32p_row03_traceSegment_040_3611_0008, g32p_row03_traceSegment_040_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3628 8 9, g32p_row03_traceSegment_040_3628_0008, g32p_row03_traceSegment_040_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3611 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3611 17 17, g32p_row03_traceSegment_040_3611_0017, g32p_row03_traceSegment_040_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 3577 68 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3577 34 34, g32p_row03_traceSegment_040_3577_0034, g32p_row03_traceSegment_040_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 3510 135 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3510 67 68, g32p_row03_traceSegment_040_3510_0067, g32p_row03_traceSegment_040_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 3645 16 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3661 8 9, g32p_row03_traceSegment_040_3661_0008, g32p_row03_traceSegment_040_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 3645 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3645 16 17, g32p_row03_traceSegment_040_3645_0016, g32p_row03_traceSegment_040_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3678 8 9, g32p_row03_traceSegment_040_3678_0008, g32p_row03_traceSegment_040_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3695 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3695 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3695 8 9, g32p_row03_traceSegment_040_3695_0008, g32p_row03_traceSegment_040_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3678 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3678 17 17, g32p_row03_traceSegment_040_3678_0017, g32p_row03_traceSegment_040_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 3645 67 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3645 33 34, g32p_row03_traceSegment_040_3645_0033, g32p_row03_traceSegment_040_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3712 8 9, g32p_row03_traceSegment_040_3712_0008, g32p_row03_traceSegment_040_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3737 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3729 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3729 8 9, g32p_row03_traceSegment_040_3729_0008, g32p_row03_traceSegment_040_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3712 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3712 17 17, g32p_row03_traceSegment_040_3712_0017, g32p_row03_traceSegment_040_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3746 8 9, g32p_row03_traceSegment_040_3746_0008, g32p_row03_traceSegment_040_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3763 8 9, g32p_row03_traceSegment_040_3763_0008, g32p_row03_traceSegment_040_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3746 17 17, g32p_row03_traceSegment_040_3746_0017, g32p_row03_traceSegment_040_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 3712 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3712 34 34, g32p_row03_traceSegment_040_3712_0034, g32p_row03_traceSegment_040_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 3645 135 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3645 67 68, g32p_row03_traceSegment_040_3645_0067, g32p_row03_traceSegment_040_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 3510 270 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3510 135 135, g32p_row03_traceSegment_040_3510_0135, g32p_row03_traceSegment_040_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_040 3240 540 = [0, 0, 0, 26] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3240 270 270, g32p_row03_traceSegment_040_3240_0270, g32p_row03_traceSegment_040_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3796 8 9, g32p_row03_traceSegment_040_3796_0008, g32p_row03_traceSegment_040_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3780 16 17, g32p_row03_traceSegment_040_3780_0016, g32p_row03_traceSegment_040_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3813 8 9, g32p_row03_traceSegment_040_3813_0008, g32p_row03_traceSegment_040_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3830 8 9, g32p_row03_traceSegment_040_3830_0008, g32p_row03_traceSegment_040_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3813 17 17, g32p_row03_traceSegment_040_3813_0017, g32p_row03_traceSegment_040_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3780 33 34, g32p_row03_traceSegment_040_3780_0033, g32p_row03_traceSegment_040_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3847 8 9, g32p_row03_traceSegment_040_3847_0008, g32p_row03_traceSegment_040_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3864 8 9, g32p_row03_traceSegment_040_3864_0008, g32p_row03_traceSegment_040_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3847 17 17, g32p_row03_traceSegment_040_3847_0017, g32p_row03_traceSegment_040_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3881 8 9, g32p_row03_traceSegment_040_3881_0008, g32p_row03_traceSegment_040_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3898 8 9, g32p_row03_traceSegment_040_3898_0008, g32p_row03_traceSegment_040_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3881 17 17, g32p_row03_traceSegment_040_3881_0017, g32p_row03_traceSegment_040_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3847 34 34, g32p_row03_traceSegment_040_3847_0034, g32p_row03_traceSegment_040_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 3780 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3780 67 68, g32p_row03_traceSegment_040_3780_0067, g32p_row03_traceSegment_040_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3931 8 9, g32p_row03_traceSegment_040_3931_0008, g32p_row03_traceSegment_040_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3915 16 17, g32p_row03_traceSegment_040_3915_0016, g32p_row03_traceSegment_040_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3948 8 9, g32p_row03_traceSegment_040_3948_0008, g32p_row03_traceSegment_040_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3965 8 9, g32p_row03_traceSegment_040_3965_0008, g32p_row03_traceSegment_040_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3948 17 17, g32p_row03_traceSegment_040_3948_0017, g32p_row03_traceSegment_040_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3915 33 34, g32p_row03_traceSegment_040_3915_0033, g32p_row03_traceSegment_040_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3982 8 9, g32p_row03_traceSegment_040_3982_0008, g32p_row03_traceSegment_040_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3999 8 9, g32p_row03_traceSegment_040_3999_0008, g32p_row03_traceSegment_040_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3982 17 17, g32p_row03_traceSegment_040_3982_0017, g32p_row03_traceSegment_040_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4016 8 9, g32p_row03_traceSegment_040_4016_0008, g32p_row03_traceSegment_040_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4033 8 9, g32p_row03_traceSegment_040_4033_0008, g32p_row03_traceSegment_040_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4016 17 17, g32p_row03_traceSegment_040_4016_0017, g32p_row03_traceSegment_040_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3982 34 34, g32p_row03_traceSegment_040_3982_0034, g32p_row03_traceSegment_040_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 3915 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3915 67 68, g32p_row03_traceSegment_040_3915_0067, g32p_row03_traceSegment_040_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 3780 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3780 135 135, g32p_row03_traceSegment_040_3780_0135, g32p_row03_traceSegment_040_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4074 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4066 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4066 8 9, g32p_row03_traceSegment_040_4066_0008, g32p_row03_traceSegment_040_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 4050 33 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4050 16 17, g32p_row03_traceSegment_040_4050_0016, g32p_row03_traceSegment_040_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4083 8 9, g32p_row03_traceSegment_040_4083_0008, g32p_row03_traceSegment_040_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4100 8 9, g32p_row03_traceSegment_040_4100_0008, g32p_row03_traceSegment_040_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4083 17 17, g32p_row03_traceSegment_040_4083_0017, g32p_row03_traceSegment_040_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 4050 67 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4050 33 34, g32p_row03_traceSegment_040_4050_0033, g32p_row03_traceSegment_040_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4117 8 9, g32p_row03_traceSegment_040_4117_0008, g32p_row03_traceSegment_040_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4142 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4134 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4134 8 9, g32p_row03_traceSegment_040_4134_0008, g32p_row03_traceSegment_040_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 4117 34 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4117 17 17, g32p_row03_traceSegment_040_4117_0017, g32p_row03_traceSegment_040_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4151 8 9, g32p_row03_traceSegment_040_4151_0008, g32p_row03_traceSegment_040_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4168 8 9, g32p_row03_traceSegment_040_4168_0008, g32p_row03_traceSegment_040_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4151 17 17, g32p_row03_traceSegment_040_4151_0017, g32p_row03_traceSegment_040_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 4117 68 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4117 34 34, g32p_row03_traceSegment_040_4117_0034, g32p_row03_traceSegment_040_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 4050 135 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4050 67 68, g32p_row03_traceSegment_040_4050_0067, g32p_row03_traceSegment_040_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_040 4185 16 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4201 8 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4209 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4201 17 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4201 8 9, g32p_row03_traceSegment_040_4201_0008, g32p_row03_traceSegment_040_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_040 4185 33 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4185 16 17, g32p_row03_traceSegment_040_4185_0016, g32p_row03_traceSegment_040_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4218 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4218 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4218 8 9, g32p_row03_traceSegment_040_4218_0008, g32p_row03_traceSegment_040_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4243 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4235 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4235 8 9, g32p_row03_traceSegment_040_4235_0008, g32p_row03_traceSegment_040_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 4218 34 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4218 17 17, g32p_row03_traceSegment_040_4218_0017, g32p_row03_traceSegment_040_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_040 4185 67 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4185 33 34, g32p_row03_traceSegment_040_4185_0033, g32p_row03_traceSegment_040_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4252 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4252 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4252 8 9, g32p_row03_traceSegment_040_4252_0008, g32p_row03_traceSegment_040_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4277 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4269 17 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4269 8 9, g32p_row03_traceSegment_040_4269_0008, g32p_row03_traceSegment_040_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 4252 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4252 17 17, g32p_row03_traceSegment_040_4252_0017, g32p_row03_traceSegment_040_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4286 8 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4294 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4286 17 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4286 8 9, g32p_row03_traceSegment_040_4286_0008, g32p_row03_traceSegment_040_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_040 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_040 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_040_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_040 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4303 8 9, g32p_row03_traceSegment_040_4303_0008, g32p_row03_traceSegment_040_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_040 4286 34 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4286 17 17, g32p_row03_traceSegment_040_4286_0017, g32p_row03_traceSegment_040_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_040 4252 68 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4252 34 34, g32p_row03_traceSegment_040_4252_0034, g32p_row03_traceSegment_040_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_040 4185 135 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4185 67 68, g32p_row03_traceSegment_040_4185_0067, g32p_row03_traceSegment_040_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_040_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_040 4050 270 = [0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 4050 135 135, g32p_row03_traceSegment_040_4050_0135, g32p_row03_traceSegment_040_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_040 3780 540 = [0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3780 270 270, g32p_row03_traceSegment_040_3780_0270, g32p_row03_traceSegment_040_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_040_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_040 3240 1080 = [0, 0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 3240 540 540, g32p_row03_traceSegment_040_3240_0540, g32p_row03_traceSegment_040_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_040_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_040 2160 2160 = [0, 0, 0, 63] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 2160 1080 1080, g32p_row03_traceSegment_040_2160_1080, g32p_row03_traceSegment_040_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_040_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_040 0 4320 = [0, 0, 0, 120] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_040 0 2160 2160, g32p_row03_traceSegment_040_0000_2160, g32p_row03_traceSegment_040_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_040 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 40 = [0, 0, 0, 120] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_040_0000_4320

end HodgeLean.Foundations.Program

end
end
