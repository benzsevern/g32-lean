import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_026 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 26 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_026_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 16 8 9, g32p_row03_traceSegment_026_0016_0008, g32p_row03_traceSegment_026_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 0 16 17, g32p_row03_traceSegment_026_0000_0016, g32p_row03_traceSegment_026_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 33 8 9, g32p_row03_traceSegment_026_0033_0008, g32p_row03_traceSegment_026_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 50 8 9, g32p_row03_traceSegment_026_0050_0008, g32p_row03_traceSegment_026_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 33 17 17, g32p_row03_traceSegment_026_0033_0017, g32p_row03_traceSegment_026_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 0 33 34, g32p_row03_traceSegment_026_0000_0033, g32p_row03_traceSegment_026_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 67 8 9, g32p_row03_traceSegment_026_0067_0008, g32p_row03_traceSegment_026_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 84 8 9, g32p_row03_traceSegment_026_0084_0008, g32p_row03_traceSegment_026_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 67 17 17, g32p_row03_traceSegment_026_0067_0017, g32p_row03_traceSegment_026_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 101 8 9, g32p_row03_traceSegment_026_0101_0008, g32p_row03_traceSegment_026_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 118 8 9, g32p_row03_traceSegment_026_0118_0008, g32p_row03_traceSegment_026_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 101 17 17, g32p_row03_traceSegment_026_0101_0017, g32p_row03_traceSegment_026_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 67 34 34, g32p_row03_traceSegment_026_0067_0034, g32p_row03_traceSegment_026_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 0 67 68, g32p_row03_traceSegment_026_0000_0067, g32p_row03_traceSegment_026_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 151 8 9, g32p_row03_traceSegment_026_0151_0008, g32p_row03_traceSegment_026_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 135 16 17, g32p_row03_traceSegment_026_0135_0016, g32p_row03_traceSegment_026_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 168 8 9, g32p_row03_traceSegment_026_0168_0008, g32p_row03_traceSegment_026_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 185 8 9, g32p_row03_traceSegment_026_0185_0008, g32p_row03_traceSegment_026_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 168 17 17, g32p_row03_traceSegment_026_0168_0017, g32p_row03_traceSegment_026_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 135 33 34, g32p_row03_traceSegment_026_0135_0033, g32p_row03_traceSegment_026_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 202 8 9, g32p_row03_traceSegment_026_0202_0008, g32p_row03_traceSegment_026_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 219 8 9, g32p_row03_traceSegment_026_0219_0008, g32p_row03_traceSegment_026_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 202 17 17, g32p_row03_traceSegment_026_0202_0017, g32p_row03_traceSegment_026_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 236 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 244 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 236 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 236 8 9, g32p_row03_traceSegment_026_0236_0008, g32p_row03_traceSegment_026_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 253 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 253 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 253 8 9, g32p_row03_traceSegment_026_0253_0008, g32p_row03_traceSegment_026_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 236 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 236 17 17, g32p_row03_traceSegment_026_0236_0017, g32p_row03_traceSegment_026_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 202 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 202 34 34, g32p_row03_traceSegment_026_0202_0034, g32p_row03_traceSegment_026_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 135 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 135 67 68, g32p_row03_traceSegment_026_0135_0067, g32p_row03_traceSegment_026_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 0 270 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 0 135 135, g32p_row03_traceSegment_026_0000_0135, g32p_row03_traceSegment_026_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 270 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 286 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 286 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 286 8 9, g32p_row03_traceSegment_026_0286_0008, g32p_row03_traceSegment_026_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 270 33 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 270 16 17, g32p_row03_traceSegment_026_0270_0016, g32p_row03_traceSegment_026_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 303 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 311 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 303 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 303 8 9, g32p_row03_traceSegment_026_0303_0008, g32p_row03_traceSegment_026_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 320 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 320 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 320 8 9, g32p_row03_traceSegment_026_0320_0008, g32p_row03_traceSegment_026_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 303 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 303 17 17, g32p_row03_traceSegment_026_0303_0017, g32p_row03_traceSegment_026_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 270 67 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 270 33 34, g32p_row03_traceSegment_026_0270_0033, g32p_row03_traceSegment_026_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 337 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 337 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 337 8 9, g32p_row03_traceSegment_026_0337_0008, g32p_row03_traceSegment_026_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 354 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 362 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 354 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 354 8 9, g32p_row03_traceSegment_026_0354_0008, g32p_row03_traceSegment_026_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 337 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 337 17 17, g32p_row03_traceSegment_026_0337_0017, g32p_row03_traceSegment_026_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 371 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 371 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 371 8 9, g32p_row03_traceSegment_026_0371_0008, g32p_row03_traceSegment_026_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 388 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 388 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 388 8 9, g32p_row03_traceSegment_026_0388_0008, g32p_row03_traceSegment_026_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 371 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 371 17 17, g32p_row03_traceSegment_026_0371_0017, g32p_row03_traceSegment_026_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 337 68 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 337 34 34, g32p_row03_traceSegment_026_0337_0034, g32p_row03_traceSegment_026_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 270 135 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 270 67 68, g32p_row03_traceSegment_026_0270_0067, g32p_row03_traceSegment_026_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 421 8 9, g32p_row03_traceSegment_026_0421_0008, g32p_row03_traceSegment_026_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 405 16 17, g32p_row03_traceSegment_026_0405_0016, g32p_row03_traceSegment_026_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 438 8 9, g32p_row03_traceSegment_026_0438_0008, g32p_row03_traceSegment_026_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 455 8 9, g32p_row03_traceSegment_026_0455_0008, g32p_row03_traceSegment_026_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 438 17 17, g32p_row03_traceSegment_026_0438_0017, g32p_row03_traceSegment_026_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 405 33 34, g32p_row03_traceSegment_026_0405_0033, g32p_row03_traceSegment_026_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 472 8 9, g32p_row03_traceSegment_026_0472_0008, g32p_row03_traceSegment_026_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 489 8 9, g32p_row03_traceSegment_026_0489_0008, g32p_row03_traceSegment_026_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 472 17 17, g32p_row03_traceSegment_026_0472_0017, g32p_row03_traceSegment_026_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 506 8 9, g32p_row03_traceSegment_026_0506_0008, g32p_row03_traceSegment_026_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 523 8 9, g32p_row03_traceSegment_026_0523_0008, g32p_row03_traceSegment_026_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 506 17 17, g32p_row03_traceSegment_026_0506_0017, g32p_row03_traceSegment_026_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 472 34 34, g32p_row03_traceSegment_026_0472_0034, g32p_row03_traceSegment_026_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 405 67 68, g32p_row03_traceSegment_026_0405_0067, g32p_row03_traceSegment_026_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 270 270 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 270 135 135, g32p_row03_traceSegment_026_0270_0135, g32p_row03_traceSegment_026_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_026 0 540 = [0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 0 270 270, g32p_row03_traceSegment_026_0000_0270, g32p_row03_traceSegment_026_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 556 8 9, g32p_row03_traceSegment_026_0556_0008, g32p_row03_traceSegment_026_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 540 16 17, g32p_row03_traceSegment_026_0540_0016, g32p_row03_traceSegment_026_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 573 8 9, g32p_row03_traceSegment_026_0573_0008, g32p_row03_traceSegment_026_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 590 8 9, g32p_row03_traceSegment_026_0590_0008, g32p_row03_traceSegment_026_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 573 17 17, g32p_row03_traceSegment_026_0573_0017, g32p_row03_traceSegment_026_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 540 33 34, g32p_row03_traceSegment_026_0540_0033, g32p_row03_traceSegment_026_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 607 8 9, g32p_row03_traceSegment_026_0607_0008, g32p_row03_traceSegment_026_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 624 8 9, g32p_row03_traceSegment_026_0624_0008, g32p_row03_traceSegment_026_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 607 17 17, g32p_row03_traceSegment_026_0607_0017, g32p_row03_traceSegment_026_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 641 8 9, g32p_row03_traceSegment_026_0641_0008, g32p_row03_traceSegment_026_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 658 8 9, g32p_row03_traceSegment_026_0658_0008, g32p_row03_traceSegment_026_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 641 17 17, g32p_row03_traceSegment_026_0641_0017, g32p_row03_traceSegment_026_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 607 34 34, g32p_row03_traceSegment_026_0607_0034, g32p_row03_traceSegment_026_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 540 67 68, g32p_row03_traceSegment_026_0540_0067, g32p_row03_traceSegment_026_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 691 8 9, g32p_row03_traceSegment_026_0691_0008, g32p_row03_traceSegment_026_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 675 16 17, g32p_row03_traceSegment_026_0675_0016, g32p_row03_traceSegment_026_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 708 8 9, g32p_row03_traceSegment_026_0708_0008, g32p_row03_traceSegment_026_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 725 8 9, g32p_row03_traceSegment_026_0725_0008, g32p_row03_traceSegment_026_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 708 17 17, g32p_row03_traceSegment_026_0708_0017, g32p_row03_traceSegment_026_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 675 33 34, g32p_row03_traceSegment_026_0675_0033, g32p_row03_traceSegment_026_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 742 8 9, g32p_row03_traceSegment_026_0742_0008, g32p_row03_traceSegment_026_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 759 8 9, g32p_row03_traceSegment_026_0759_0008, g32p_row03_traceSegment_026_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 742 17 17, g32p_row03_traceSegment_026_0742_0017, g32p_row03_traceSegment_026_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 776 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 784 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 776 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 776 8 9, g32p_row03_traceSegment_026_0776_0008, g32p_row03_traceSegment_026_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 793 8 9, g32p_row03_traceSegment_026_0793_0008, g32p_row03_traceSegment_026_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 776 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 776 17 17, g32p_row03_traceSegment_026_0776_0017, g32p_row03_traceSegment_026_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 742 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 742 34 34, g32p_row03_traceSegment_026_0742_0034, g32p_row03_traceSegment_026_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 675 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 675 67 68, g32p_row03_traceSegment_026_0675_0067, g32p_row03_traceSegment_026_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 540 270 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 540 135 135, g32p_row03_traceSegment_026_0540_0135, g32p_row03_traceSegment_026_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 826 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 826 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 826 8 9, g32p_row03_traceSegment_026_0826_0008, g32p_row03_traceSegment_026_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 810 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 810 16 17, g32p_row03_traceSegment_026_0810_0016, g32p_row03_traceSegment_026_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 843 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 843 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 843 8 9, g32p_row03_traceSegment_026_0843_0008, g32p_row03_traceSegment_026_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 860 8 9, g32p_row03_traceSegment_026_0860_0008, g32p_row03_traceSegment_026_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 843 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 843 17 17, g32p_row03_traceSegment_026_0843_0017, g32p_row03_traceSegment_026_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 810 67 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 810 33 34, g32p_row03_traceSegment_026_0810_0033, g32p_row03_traceSegment_026_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 885 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 877 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 877 8 9, g32p_row03_traceSegment_026_0877_0008, g32p_row03_traceSegment_026_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 902 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 894 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 894 8 9, g32p_row03_traceSegment_026_0894_0008, g32p_row03_traceSegment_026_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 877 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 877 17 17, g32p_row03_traceSegment_026_0877_0017, g32p_row03_traceSegment_026_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 919 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 911 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 911 8 9, g32p_row03_traceSegment_026_0911_0008, g32p_row03_traceSegment_026_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 928 8 9, g32p_row03_traceSegment_026_0928_0008, g32p_row03_traceSegment_026_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 911 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 911 17 17, g32p_row03_traceSegment_026_0911_0017, g32p_row03_traceSegment_026_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 877 68 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 877 34 34, g32p_row03_traceSegment_026_0877_0034, g32p_row03_traceSegment_026_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 810 135 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 810 67 68, g32p_row03_traceSegment_026_0810_0067, g32p_row03_traceSegment_026_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 945 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 961 8 9, g32p_row03_traceSegment_026_0961_0008, g32p_row03_traceSegment_026_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 945 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 945 16 17, g32p_row03_traceSegment_026_0945_0016, g32p_row03_traceSegment_026_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 978 8 9, g32p_row03_traceSegment_026_0978_0008, g32p_row03_traceSegment_026_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 995 8 9, g32p_row03_traceSegment_026_0995_0008, g32p_row03_traceSegment_026_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 978 17 17, g32p_row03_traceSegment_026_0978_0017, g32p_row03_traceSegment_026_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 945 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 945 33 34, g32p_row03_traceSegment_026_0945_0033, g32p_row03_traceSegment_026_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1020 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1012 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1012 8 9, g32p_row03_traceSegment_026_1012_0008, g32p_row03_traceSegment_026_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1029 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1037 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1029 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1029 8 9, g32p_row03_traceSegment_026_1029_0008, g32p_row03_traceSegment_026_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1012 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1012 17 17, g32p_row03_traceSegment_026_1012_0017, g32p_row03_traceSegment_026_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1046 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1046 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1046 8 9, g32p_row03_traceSegment_026_1046_0008, g32p_row03_traceSegment_026_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1071 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1063 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1063 8 9, g32p_row03_traceSegment_026_1063_0008, g32p_row03_traceSegment_026_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1046 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1046 17 17, g32p_row03_traceSegment_026_1046_0017, g32p_row03_traceSegment_026_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 1012 68 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1012 34 34, g32p_row03_traceSegment_026_1012_0034, g32p_row03_traceSegment_026_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 945 135 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 945 67 68, g32p_row03_traceSegment_026_0945_0067, g32p_row03_traceSegment_026_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 810 270 = [0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 810 135 135, g32p_row03_traceSegment_026_0810_0135, g32p_row03_traceSegment_026_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_026 540 540 = [0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 540 270 270, g32p_row03_traceSegment_026_0540_0270, g32p_row03_traceSegment_026_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_026 0 1080 = [0, 0, 33] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 0 540 540, g32p_row03_traceSegment_026_0000_0540, g32p_row03_traceSegment_026_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 1080 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1096 8 9, g32p_row03_traceSegment_026_1096_0008, g32p_row03_traceSegment_026_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 1080 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1080 16 17, g32p_row03_traceSegment_026_1080_0016, g32p_row03_traceSegment_026_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1113 8 9, g32p_row03_traceSegment_026_1113_0008, g32p_row03_traceSegment_026_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1138 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1130 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1130 8 9, g32p_row03_traceSegment_026_1130_0008, g32p_row03_traceSegment_026_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1113 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1113 17 17, g32p_row03_traceSegment_026_1113_0017, g32p_row03_traceSegment_026_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 1080 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1080 33 34, g32p_row03_traceSegment_026_1080_0033, g32p_row03_traceSegment_026_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1155 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1147 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1147 8 9, g32p_row03_traceSegment_026_1147_0008, g32p_row03_traceSegment_026_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1164 8 9, g32p_row03_traceSegment_026_1164_0008, g32p_row03_traceSegment_026_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1147 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1147 17 17, g32p_row03_traceSegment_026_1147_0017, g32p_row03_traceSegment_026_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1181 8 9, g32p_row03_traceSegment_026_1181_0008, g32p_row03_traceSegment_026_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1198 8 9, g32p_row03_traceSegment_026_1198_0008, g32p_row03_traceSegment_026_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1181 17 17, g32p_row03_traceSegment_026_1181_0017, g32p_row03_traceSegment_026_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 1147 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1147 34 34, g32p_row03_traceSegment_026_1147_0034, g32p_row03_traceSegment_026_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 1080 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1080 67 68, g32p_row03_traceSegment_026_1080_0067, g32p_row03_traceSegment_026_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1231 8 9, g32p_row03_traceSegment_026_1231_0008, g32p_row03_traceSegment_026_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1215 16 17, g32p_row03_traceSegment_026_1215_0016, g32p_row03_traceSegment_026_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1248 8 9, g32p_row03_traceSegment_026_1248_0008, g32p_row03_traceSegment_026_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1265 8 9, g32p_row03_traceSegment_026_1265_0008, g32p_row03_traceSegment_026_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1248 17 17, g32p_row03_traceSegment_026_1248_0017, g32p_row03_traceSegment_026_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1215 33 34, g32p_row03_traceSegment_026_1215_0033, g32p_row03_traceSegment_026_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1282 8 9, g32p_row03_traceSegment_026_1282_0008, g32p_row03_traceSegment_026_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1299 8 9, g32p_row03_traceSegment_026_1299_0008, g32p_row03_traceSegment_026_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1282 17 17, g32p_row03_traceSegment_026_1282_0017, g32p_row03_traceSegment_026_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1316 8 9, g32p_row03_traceSegment_026_1316_0008, g32p_row03_traceSegment_026_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1333 8 9, g32p_row03_traceSegment_026_1333_0008, g32p_row03_traceSegment_026_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1316 17 17, g32p_row03_traceSegment_026_1316_0017, g32p_row03_traceSegment_026_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1282 34 34, g32p_row03_traceSegment_026_1282_0034, g32p_row03_traceSegment_026_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1215 67 68, g32p_row03_traceSegment_026_1215_0067, g32p_row03_traceSegment_026_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 1080 270 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1080 135 135, g32p_row03_traceSegment_026_1080_0135, g32p_row03_traceSegment_026_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1366 8 9, g32p_row03_traceSegment_026_1366_0008, g32p_row03_traceSegment_026_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1350 16 17, g32p_row03_traceSegment_026_1350_0016, g32p_row03_traceSegment_026_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1383 8 9, g32p_row03_traceSegment_026_1383_0008, g32p_row03_traceSegment_026_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1400 8 9, g32p_row03_traceSegment_026_1400_0008, g32p_row03_traceSegment_026_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1383 17 17, g32p_row03_traceSegment_026_1383_0017, g32p_row03_traceSegment_026_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1350 33 34, g32p_row03_traceSegment_026_1350_0033, g32p_row03_traceSegment_026_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1417 8 9, g32p_row03_traceSegment_026_1417_0008, g32p_row03_traceSegment_026_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1434 8 9, g32p_row03_traceSegment_026_1434_0008, g32p_row03_traceSegment_026_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1417 17 17, g32p_row03_traceSegment_026_1417_0017, g32p_row03_traceSegment_026_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1459 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1451 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1451 8 9, g32p_row03_traceSegment_026_1451_0008, g32p_row03_traceSegment_026_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1468 8 9, g32p_row03_traceSegment_026_1468_0008, g32p_row03_traceSegment_026_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1451 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1451 17 17, g32p_row03_traceSegment_026_1451_0017, g32p_row03_traceSegment_026_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 1417 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1417 34 34, g32p_row03_traceSegment_026_1417_0034, g32p_row03_traceSegment_026_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 1350 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1350 67 68, g32p_row03_traceSegment_026_1350_0067, g32p_row03_traceSegment_026_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 1485 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1509 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1501 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1501 8 9, g32p_row03_traceSegment_026_1501_0008, g32p_row03_traceSegment_026_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 1485 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1485 16 17, g32p_row03_traceSegment_026_1485_0016, g32p_row03_traceSegment_026_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1518 8 9, g32p_row03_traceSegment_026_1518_0008, g32p_row03_traceSegment_026_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1535 8 9, g32p_row03_traceSegment_026_1535_0008, g32p_row03_traceSegment_026_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1518 17 17, g32p_row03_traceSegment_026_1518_0017, g32p_row03_traceSegment_026_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 1485 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1485 33 34, g32p_row03_traceSegment_026_1485_0033, g32p_row03_traceSegment_026_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1552 8 9, g32p_row03_traceSegment_026_1552_0008, g32p_row03_traceSegment_026_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1569 8 9, g32p_row03_traceSegment_026_1569_0008, g32p_row03_traceSegment_026_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1552 17 17, g32p_row03_traceSegment_026_1552_0017, g32p_row03_traceSegment_026_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1586 8 9, g32p_row03_traceSegment_026_1586_0008, g32p_row03_traceSegment_026_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1603 8 9, g32p_row03_traceSegment_026_1603_0008, g32p_row03_traceSegment_026_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1586 17 17, g32p_row03_traceSegment_026_1586_0017, g32p_row03_traceSegment_026_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1552 34 34, g32p_row03_traceSegment_026_1552_0034, g32p_row03_traceSegment_026_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 1485 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1485 67 68, g32p_row03_traceSegment_026_1485_0067, g32p_row03_traceSegment_026_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 1350 270 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1350 135 135, g32p_row03_traceSegment_026_1350_0135, g32p_row03_traceSegment_026_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_026 1080 540 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1080 270 270, g32p_row03_traceSegment_026_1080_0270, g32p_row03_traceSegment_026_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 1620 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1644 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1636 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1636 8 9, g32p_row03_traceSegment_026_1636_0008, g32p_row03_traceSegment_026_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 1620 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1620 16 17, g32p_row03_traceSegment_026_1620_0016, g32p_row03_traceSegment_026_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1653 8 9, g32p_row03_traceSegment_026_1653_0008, g32p_row03_traceSegment_026_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1670 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1678 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1670 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1670 8 9, g32p_row03_traceSegment_026_1670_0008, g32p_row03_traceSegment_026_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1653 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1653 17 17, g32p_row03_traceSegment_026_1653_0017, g32p_row03_traceSegment_026_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 1620 67 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1620 33 34, g32p_row03_traceSegment_026_1620_0033, g32p_row03_traceSegment_026_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1687 8 9, g32p_row03_traceSegment_026_1687_0008, g32p_row03_traceSegment_026_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1704 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1704 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1704 8 9, g32p_row03_traceSegment_026_1704_0008, g32p_row03_traceSegment_026_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1687 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1687 17 17, g32p_row03_traceSegment_026_1687_0017, g32p_row03_traceSegment_026_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1721 8 9, g32p_row03_traceSegment_026_1721_0008, g32p_row03_traceSegment_026_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1738 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1738 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1738 8 9, g32p_row03_traceSegment_026_1738_0008, g32p_row03_traceSegment_026_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1721 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1721 17 17, g32p_row03_traceSegment_026_1721_0017, g32p_row03_traceSegment_026_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 1687 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1687 34 34, g32p_row03_traceSegment_026_1687_0034, g32p_row03_traceSegment_026_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 1620 135 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1620 67 68, g32p_row03_traceSegment_026_1620_0067, g32p_row03_traceSegment_026_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1771 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1771 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1771 8 9, g32p_row03_traceSegment_026_1771_0008, g32p_row03_traceSegment_026_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 1755 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1755 16 17, g32p_row03_traceSegment_026_1755_0016, g32p_row03_traceSegment_026_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1788 8 9, g32p_row03_traceSegment_026_1788_0008, g32p_row03_traceSegment_026_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1805 8 9, g32p_row03_traceSegment_026_1805_0008, g32p_row03_traceSegment_026_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1788 17 17, g32p_row03_traceSegment_026_1788_0017, g32p_row03_traceSegment_026_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 1755 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1755 33 34, g32p_row03_traceSegment_026_1755_0033, g32p_row03_traceSegment_026_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1830 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1822 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1822 8 9, g32p_row03_traceSegment_026_1822_0008, g32p_row03_traceSegment_026_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1839 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1839 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1839 8 9, g32p_row03_traceSegment_026_1839_0008, g32p_row03_traceSegment_026_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1822 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1822 17 17, g32p_row03_traceSegment_026_1822_0017, g32p_row03_traceSegment_026_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1856 8 9, g32p_row03_traceSegment_026_1856_0008, g32p_row03_traceSegment_026_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1873 8 9, g32p_row03_traceSegment_026_1873_0008, g32p_row03_traceSegment_026_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1856 17 17, g32p_row03_traceSegment_026_1856_0017, g32p_row03_traceSegment_026_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 1822 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1822 34 34, g32p_row03_traceSegment_026_1822_0034, g32p_row03_traceSegment_026_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 1755 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1755 67 68, g32p_row03_traceSegment_026_1755_0067, g32p_row03_traceSegment_026_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 1620 270 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1620 135 135, g32p_row03_traceSegment_026_1620_0135, g32p_row03_traceSegment_026_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 1890 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1906 8 9, g32p_row03_traceSegment_026_1906_0008, g32p_row03_traceSegment_026_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 1890 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1890 16 17, g32p_row03_traceSegment_026_1890_0016, g32p_row03_traceSegment_026_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1923 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1923 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1923 8 9, g32p_row03_traceSegment_026_1923_0008, g32p_row03_traceSegment_026_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1940 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1948 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1940 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1940 8 9, g32p_row03_traceSegment_026_1940_0008, g32p_row03_traceSegment_026_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1923 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1923 17 17, g32p_row03_traceSegment_026_1923_0017, g32p_row03_traceSegment_026_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 1890 67 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1890 33 34, g32p_row03_traceSegment_026_1890_0033, g32p_row03_traceSegment_026_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1965 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1957 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1957 8 9, g32p_row03_traceSegment_026_1957_0008, g32p_row03_traceSegment_026_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1982 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1974 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1974 8 9, g32p_row03_traceSegment_026_1974_0008, g32p_row03_traceSegment_026_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1957 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1957 17 17, g32p_row03_traceSegment_026_1957_0017, g32p_row03_traceSegment_026_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 1991 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 1999 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 1991 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1991 8 9, g32p_row03_traceSegment_026_1991_0008, g32p_row03_traceSegment_026_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2016 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2008 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2008 8 9, g32p_row03_traceSegment_026_2008_0008, g32p_row03_traceSegment_026_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 1991 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1991 17 17, g32p_row03_traceSegment_026_1991_0017, g32p_row03_traceSegment_026_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 1957 68 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1957 34 34, g32p_row03_traceSegment_026_1957_0034, g32p_row03_traceSegment_026_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 1890 135 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1890 67 68, g32p_row03_traceSegment_026_1890_0067, g32p_row03_traceSegment_026_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 2025 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2041 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2041 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2041 8 9, g32p_row03_traceSegment_026_2041_0008, g32p_row03_traceSegment_026_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 2025 33 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2025 16 17, g32p_row03_traceSegment_026_2025_0016, g32p_row03_traceSegment_026_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2058 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2066 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2058 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2058 8 9, g32p_row03_traceSegment_026_2058_0008, g32p_row03_traceSegment_026_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2075 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2083 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2075 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2075 8 9, g32p_row03_traceSegment_026_2075_0008, g32p_row03_traceSegment_026_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2058 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2058 17 17, g32p_row03_traceSegment_026_2058_0017, g32p_row03_traceSegment_026_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 2025 67 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2025 33 34, g32p_row03_traceSegment_026_2025_0033, g32p_row03_traceSegment_026_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2100 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2092 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2092 8 9, g32p_row03_traceSegment_026_2092_0008, g32p_row03_traceSegment_026_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2117 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2109 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2109 8 9, g32p_row03_traceSegment_026_2109_0008, g32p_row03_traceSegment_026_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2092 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2092 17 17, g32p_row03_traceSegment_026_2092_0017, g32p_row03_traceSegment_026_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2134 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2126 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2126 8 9, g32p_row03_traceSegment_026_2126_0008, g32p_row03_traceSegment_026_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2143 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2151 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2143 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2143 8 9, g32p_row03_traceSegment_026_2143_0008, g32p_row03_traceSegment_026_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2126 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2126 17 17, g32p_row03_traceSegment_026_2126_0017, g32p_row03_traceSegment_026_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 2092 68 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2092 34 34, g32p_row03_traceSegment_026_2092_0034, g32p_row03_traceSegment_026_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 2025 135 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2025 67 68, g32p_row03_traceSegment_026_2025_0067, g32p_row03_traceSegment_026_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 1890 270 = [0, 0, 25] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1890 135 135, g32p_row03_traceSegment_026_1890_0135, g32p_row03_traceSegment_026_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_026 1620 540 = [0, 0, 34] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1620 270 270, g32p_row03_traceSegment_026_1620_0270, g32p_row03_traceSegment_026_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_026_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_026 1080 1080 = [0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 1080 540 540, g32p_row03_traceSegment_026_1080_0540, g32p_row03_traceSegment_026_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_026 0 2160 = [0, 0, 73] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 0 1080 1080, g32p_row03_traceSegment_026_0000_1080, g32p_row03_traceSegment_026_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2176 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2176 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2176 8 9, g32p_row03_traceSegment_026_2176_0008, g32p_row03_traceSegment_026_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 2160 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2160 16 17, g32p_row03_traceSegment_026_2160_0016, g32p_row03_traceSegment_026_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2193 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2193 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2193 8 9, g32p_row03_traceSegment_026_2193_0008, g32p_row03_traceSegment_026_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2218 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2210 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2210 8 9, g32p_row03_traceSegment_026_2210_0008, g32p_row03_traceSegment_026_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2193 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2193 17 17, g32p_row03_traceSegment_026_2193_0017, g32p_row03_traceSegment_026_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 2160 67 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2160 33 34, g32p_row03_traceSegment_026_2160_0033, g32p_row03_traceSegment_026_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2227 8 9, g32p_row03_traceSegment_026_2227_0008, g32p_row03_traceSegment_026_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2244 8 9, g32p_row03_traceSegment_026_2244_0008, g32p_row03_traceSegment_026_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2227 17 17, g32p_row03_traceSegment_026_2227_0017, g32p_row03_traceSegment_026_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2261 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2261 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2261 8 9, g32p_row03_traceSegment_026_2261_0008, g32p_row03_traceSegment_026_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2278 8 9, g32p_row03_traceSegment_026_2278_0008, g32p_row03_traceSegment_026_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2261 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2261 17 17, g32p_row03_traceSegment_026_2261_0017, g32p_row03_traceSegment_026_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 2227 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2227 34 34, g32p_row03_traceSegment_026_2227_0034, g32p_row03_traceSegment_026_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 2160 135 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2160 67 68, g32p_row03_traceSegment_026_2160_0067, g32p_row03_traceSegment_026_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2311 8 9, g32p_row03_traceSegment_026_2311_0008, g32p_row03_traceSegment_026_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2295 16 17, g32p_row03_traceSegment_026_2295_0016, g32p_row03_traceSegment_026_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2328 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2328 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2328 8 9, g32p_row03_traceSegment_026_2328_0008, g32p_row03_traceSegment_026_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2353 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2345 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2345 8 9, g32p_row03_traceSegment_026_2345_0008, g32p_row03_traceSegment_026_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2328 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2328 17 17, g32p_row03_traceSegment_026_2328_0017, g32p_row03_traceSegment_026_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 2295 67 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2295 33 34, g32p_row03_traceSegment_026_2295_0033, g32p_row03_traceSegment_026_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2362 8 9, g32p_row03_traceSegment_026_2362_0008, g32p_row03_traceSegment_026_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2379 8 9, g32p_row03_traceSegment_026_2379_0008, g32p_row03_traceSegment_026_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2362 17 17, g32p_row03_traceSegment_026_2362_0017, g32p_row03_traceSegment_026_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2404 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2396 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2396 8 9, g32p_row03_traceSegment_026_2396_0008, g32p_row03_traceSegment_026_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2413 8 9, g32p_row03_traceSegment_026_2413_0008, g32p_row03_traceSegment_026_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2396 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2396 17 17, g32p_row03_traceSegment_026_2396_0017, g32p_row03_traceSegment_026_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 2362 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2362 34 34, g32p_row03_traceSegment_026_2362_0034, g32p_row03_traceSegment_026_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 2295 135 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2295 67 68, g32p_row03_traceSegment_026_2295_0067, g32p_row03_traceSegment_026_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 2160 270 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2160 135 135, g32p_row03_traceSegment_026_2160_0135, g32p_row03_traceSegment_026_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 2430 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2446 8 9, g32p_row03_traceSegment_026_2446_0008, g32p_row03_traceSegment_026_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 2430 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2430 16 17, g32p_row03_traceSegment_026_2430_0016, g32p_row03_traceSegment_026_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2463 8 9, g32p_row03_traceSegment_026_2463_0008, g32p_row03_traceSegment_026_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2480 8 9, g32p_row03_traceSegment_026_2480_0008, g32p_row03_traceSegment_026_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2463 17 17, g32p_row03_traceSegment_026_2463_0017, g32p_row03_traceSegment_026_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 2430 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2430 33 34, g32p_row03_traceSegment_026_2430_0033, g32p_row03_traceSegment_026_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2497 8 9, g32p_row03_traceSegment_026_2497_0008, g32p_row03_traceSegment_026_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2514 8 9, g32p_row03_traceSegment_026_2514_0008, g32p_row03_traceSegment_026_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2497 17 17, g32p_row03_traceSegment_026_2497_0017, g32p_row03_traceSegment_026_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2531 8 9, g32p_row03_traceSegment_026_2531_0008, g32p_row03_traceSegment_026_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2548 8 9, g32p_row03_traceSegment_026_2548_0008, g32p_row03_traceSegment_026_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2531 17 17, g32p_row03_traceSegment_026_2531_0017, g32p_row03_traceSegment_026_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2497 34 34, g32p_row03_traceSegment_026_2497_0034, g32p_row03_traceSegment_026_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 2430 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2430 67 68, g32p_row03_traceSegment_026_2430_0067, g32p_row03_traceSegment_026_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 2565 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2581 8 9, g32p_row03_traceSegment_026_2581_0008, g32p_row03_traceSegment_026_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 2565 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2565 16 17, g32p_row03_traceSegment_026_2565_0016, g32p_row03_traceSegment_026_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2606 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2598 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2598 8 9, g32p_row03_traceSegment_026_2598_0008, g32p_row03_traceSegment_026_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2615 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2615 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2615 8 9, g32p_row03_traceSegment_026_2615_0008, g32p_row03_traceSegment_026_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2598 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2598 17 17, g32p_row03_traceSegment_026_2598_0017, g32p_row03_traceSegment_026_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 2565 67 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2565 33 34, g32p_row03_traceSegment_026_2565_0033, g32p_row03_traceSegment_026_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2632 8 9, g32p_row03_traceSegment_026_2632_0008, g32p_row03_traceSegment_026_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2649 8 9, g32p_row03_traceSegment_026_2649_0008, g32p_row03_traceSegment_026_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2632 17 17, g32p_row03_traceSegment_026_2632_0017, g32p_row03_traceSegment_026_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2666 8 9, g32p_row03_traceSegment_026_2666_0008, g32p_row03_traceSegment_026_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2683 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2683 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2683 8 9, g32p_row03_traceSegment_026_2683_0008, g32p_row03_traceSegment_026_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2666 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2666 17 17, g32p_row03_traceSegment_026_2666_0017, g32p_row03_traceSegment_026_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 2632 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2632 34 34, g32p_row03_traceSegment_026_2632_0034, g32p_row03_traceSegment_026_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 2565 135 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2565 67 68, g32p_row03_traceSegment_026_2565_0067, g32p_row03_traceSegment_026_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 2430 270 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2430 135 135, g32p_row03_traceSegment_026_2430_0135, g32p_row03_traceSegment_026_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_026 2160 540 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2160 270 270, g32p_row03_traceSegment_026_2160_0270, g32p_row03_traceSegment_026_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2716 8 9, g32p_row03_traceSegment_026_2716_0008, g32p_row03_traceSegment_026_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2700 16 17, g32p_row03_traceSegment_026_2700_0016, g32p_row03_traceSegment_026_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2733 8 9, g32p_row03_traceSegment_026_2733_0008, g32p_row03_traceSegment_026_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2750 8 9, g32p_row03_traceSegment_026_2750_0008, g32p_row03_traceSegment_026_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2733 17 17, g32p_row03_traceSegment_026_2733_0017, g32p_row03_traceSegment_026_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2700 33 34, g32p_row03_traceSegment_026_2700_0033, g32p_row03_traceSegment_026_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2767 8 9, g32p_row03_traceSegment_026_2767_0008, g32p_row03_traceSegment_026_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2784 8 9, g32p_row03_traceSegment_026_2784_0008, g32p_row03_traceSegment_026_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2767 17 17, g32p_row03_traceSegment_026_2767_0017, g32p_row03_traceSegment_026_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2801 8 9, g32p_row03_traceSegment_026_2801_0008, g32p_row03_traceSegment_026_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2818 8 9, g32p_row03_traceSegment_026_2818_0008, g32p_row03_traceSegment_026_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2801 17 17, g32p_row03_traceSegment_026_2801_0017, g32p_row03_traceSegment_026_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2767 34 34, g32p_row03_traceSegment_026_2767_0034, g32p_row03_traceSegment_026_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 2700 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2700 67 68, g32p_row03_traceSegment_026_2700_0067, g32p_row03_traceSegment_026_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2851 8 9, g32p_row03_traceSegment_026_2851_0008, g32p_row03_traceSegment_026_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2835 16 17, g32p_row03_traceSegment_026_2835_0016, g32p_row03_traceSegment_026_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2868 8 9, g32p_row03_traceSegment_026_2868_0008, g32p_row03_traceSegment_026_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2885 8 9, g32p_row03_traceSegment_026_2885_0008, g32p_row03_traceSegment_026_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2868 17 17, g32p_row03_traceSegment_026_2868_0017, g32p_row03_traceSegment_026_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2835 33 34, g32p_row03_traceSegment_026_2835_0033, g32p_row03_traceSegment_026_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2902 8 9, g32p_row03_traceSegment_026_2902_0008, g32p_row03_traceSegment_026_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2919 8 9, g32p_row03_traceSegment_026_2919_0008, g32p_row03_traceSegment_026_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2902 17 17, g32p_row03_traceSegment_026_2902_0017, g32p_row03_traceSegment_026_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2936 8 9, g32p_row03_traceSegment_026_2936_0008, g32p_row03_traceSegment_026_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2953 8 9, g32p_row03_traceSegment_026_2953_0008, g32p_row03_traceSegment_026_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2936 17 17, g32p_row03_traceSegment_026_2936_0017, g32p_row03_traceSegment_026_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2902 34 34, g32p_row03_traceSegment_026_2902_0034, g32p_row03_traceSegment_026_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2835 67 68, g32p_row03_traceSegment_026_2835_0067, g32p_row03_traceSegment_026_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 2700 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2700 135 135, g32p_row03_traceSegment_026_2700_0135, g32p_row03_traceSegment_026_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2986 8 9, g32p_row03_traceSegment_026_2986_0008, g32p_row03_traceSegment_026_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2970 16 17, g32p_row03_traceSegment_026_2970_0016, g32p_row03_traceSegment_026_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3003 8 9, g32p_row03_traceSegment_026_3003_0008, g32p_row03_traceSegment_026_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3020 8 9, g32p_row03_traceSegment_026_3020_0008, g32p_row03_traceSegment_026_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3003 17 17, g32p_row03_traceSegment_026_3003_0017, g32p_row03_traceSegment_026_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2970 33 34, g32p_row03_traceSegment_026_2970_0033, g32p_row03_traceSegment_026_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3037 8 9, g32p_row03_traceSegment_026_3037_0008, g32p_row03_traceSegment_026_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3054 8 9, g32p_row03_traceSegment_026_3054_0008, g32p_row03_traceSegment_026_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3037 17 17, g32p_row03_traceSegment_026_3037_0017, g32p_row03_traceSegment_026_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3071 8 9, g32p_row03_traceSegment_026_3071_0008, g32p_row03_traceSegment_026_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3096 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3088 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3088 8 9, g32p_row03_traceSegment_026_3088_0008, g32p_row03_traceSegment_026_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3071 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3071 17 17, g32p_row03_traceSegment_026_3071_0017, g32p_row03_traceSegment_026_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 3037 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3037 34 34, g32p_row03_traceSegment_026_3037_0034, g32p_row03_traceSegment_026_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 2970 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2970 67 68, g32p_row03_traceSegment_026_2970_0067, g32p_row03_traceSegment_026_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 3105 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3121 8 9, g32p_row03_traceSegment_026_3121_0008, g32p_row03_traceSegment_026_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 3105 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3105 16 17, g32p_row03_traceSegment_026_3105_0016, g32p_row03_traceSegment_026_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3138 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3138 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3138 8 9, g32p_row03_traceSegment_026_3138_0008, g32p_row03_traceSegment_026_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3155 8 9, g32p_row03_traceSegment_026_3155_0008, g32p_row03_traceSegment_026_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3138 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3138 17 17, g32p_row03_traceSegment_026_3138_0017, g32p_row03_traceSegment_026_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 3105 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3105 33 34, g32p_row03_traceSegment_026_3105_0033, g32p_row03_traceSegment_026_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3172 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3180 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3172 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3172 8 9, g32p_row03_traceSegment_026_3172_0008, g32p_row03_traceSegment_026_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3189 8 9, g32p_row03_traceSegment_026_3189_0008, g32p_row03_traceSegment_026_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3172 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3172 17 17, g32p_row03_traceSegment_026_3172_0017, g32p_row03_traceSegment_026_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3206 8 9, g32p_row03_traceSegment_026_3206_0008, g32p_row03_traceSegment_026_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3231 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3223 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3223 8 9, g32p_row03_traceSegment_026_3223_0008, g32p_row03_traceSegment_026_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3206 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3206 17 17, g32p_row03_traceSegment_026_3206_0017, g32p_row03_traceSegment_026_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 3172 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3172 34 34, g32p_row03_traceSegment_026_3172_0034, g32p_row03_traceSegment_026_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 3105 135 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3105 67 68, g32p_row03_traceSegment_026_3105_0067, g32p_row03_traceSegment_026_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 2970 270 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2970 135 135, g32p_row03_traceSegment_026_2970_0135, g32p_row03_traceSegment_026_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_026 2700 540 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2700 270 270, g32p_row03_traceSegment_026_2700_0270, g32p_row03_traceSegment_026_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_026 2160 1080 = [0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2160 540 540, g32p_row03_traceSegment_026_2160_0540, g32p_row03_traceSegment_026_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 3240 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3256 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3264 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3256 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3256 8 9, g32p_row03_traceSegment_026_3256_0008, g32p_row03_traceSegment_026_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 3240 33 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3240 16 17, g32p_row03_traceSegment_026_3240_0016, g32p_row03_traceSegment_026_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3281 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3273 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3273 8 9, g32p_row03_traceSegment_026_3273_0008, g32p_row03_traceSegment_026_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3290 8 9, g32p_row03_traceSegment_026_3290_0008, g32p_row03_traceSegment_026_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3273 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3273 17 17, g32p_row03_traceSegment_026_3273_0017, g32p_row03_traceSegment_026_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 3240 67 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3240 33 34, g32p_row03_traceSegment_026_3240_0033, g32p_row03_traceSegment_026_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3307 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3307 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3307 8 9, g32p_row03_traceSegment_026_3307_0008, g32p_row03_traceSegment_026_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3332 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3324 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3324 8 9, g32p_row03_traceSegment_026_3324_0008, g32p_row03_traceSegment_026_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3307 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3307 17 17, g32p_row03_traceSegment_026_3307_0017, g32p_row03_traceSegment_026_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3349 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3341 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3341 8 9, g32p_row03_traceSegment_026_3341_0008, g32p_row03_traceSegment_026_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3358 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3366 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3358 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3358 8 9, g32p_row03_traceSegment_026_3358_0008, g32p_row03_traceSegment_026_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3341 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3341 17 17, g32p_row03_traceSegment_026_3341_0017, g32p_row03_traceSegment_026_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 3307 68 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3307 34 34, g32p_row03_traceSegment_026_3307_0034, g32p_row03_traceSegment_026_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 3240 135 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3240 67 68, g32p_row03_traceSegment_026_3240_0067, g32p_row03_traceSegment_026_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 3375 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3391 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3399 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3391 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3391 8 9, g32p_row03_traceSegment_026_3391_0008, g32p_row03_traceSegment_026_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 3375 33 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3375 16 17, g32p_row03_traceSegment_026_3375_0016, g32p_row03_traceSegment_026_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3408 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3408 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3408 8 9, g32p_row03_traceSegment_026_3408_0008, g32p_row03_traceSegment_026_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3433 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3425 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3425 8 9, g32p_row03_traceSegment_026_3425_0008, g32p_row03_traceSegment_026_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3408 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3408 17 17, g32p_row03_traceSegment_026_3408_0017, g32p_row03_traceSegment_026_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 3375 67 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3375 33 34, g32p_row03_traceSegment_026_3375_0033, g32p_row03_traceSegment_026_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3442 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3442 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3442 8 9, g32p_row03_traceSegment_026_3442_0008, g32p_row03_traceSegment_026_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3459 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3467 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3459 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3459 8 9, g32p_row03_traceSegment_026_3459_0008, g32p_row03_traceSegment_026_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3442 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3442 17 17, g32p_row03_traceSegment_026_3442_0017, g32p_row03_traceSegment_026_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3476 8 9, g32p_row03_traceSegment_026_3476_0008, g32p_row03_traceSegment_026_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3493 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3493 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3493 8 9, g32p_row03_traceSegment_026_3493_0008, g32p_row03_traceSegment_026_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3476 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3476 17 17, g32p_row03_traceSegment_026_3476_0017, g32p_row03_traceSegment_026_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 3442 68 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3442 34 34, g32p_row03_traceSegment_026_3442_0034, g32p_row03_traceSegment_026_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 3375 135 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3375 67 68, g32p_row03_traceSegment_026_3375_0067, g32p_row03_traceSegment_026_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 3240 270 = [0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3240 135 135, g32p_row03_traceSegment_026_3240_0135, g32p_row03_traceSegment_026_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 3510 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3534 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3526 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3526 8 9, g32p_row03_traceSegment_026_3526_0008, g32p_row03_traceSegment_026_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 3510 33 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3510 16 17, g32p_row03_traceSegment_026_3510_0016, g32p_row03_traceSegment_026_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3543 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3551 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3543 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3543 8 9, g32p_row03_traceSegment_026_3543_0008, g32p_row03_traceSegment_026_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3560 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3560 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3560 8 9, g32p_row03_traceSegment_026_3560_0008, g32p_row03_traceSegment_026_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3543 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3543 17 17, g32p_row03_traceSegment_026_3543_0017, g32p_row03_traceSegment_026_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 3510 67 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3510 33 34, g32p_row03_traceSegment_026_3510_0033, g32p_row03_traceSegment_026_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3577 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3585 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3577 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3577 8 9, g32p_row03_traceSegment_026_3577_0008, g32p_row03_traceSegment_026_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3594 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3602 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3594 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3594 8 9, g32p_row03_traceSegment_026_3594_0008, g32p_row03_traceSegment_026_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3577 34 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3577 17 17, g32p_row03_traceSegment_026_3577_0017, g32p_row03_traceSegment_026_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3619 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3611 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3611 8 9, g32p_row03_traceSegment_026_3611_0008, g32p_row03_traceSegment_026_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3628 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3636 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3628 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3628 8 9, g32p_row03_traceSegment_026_3628_0008, g32p_row03_traceSegment_026_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3611 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3611 17 17, g32p_row03_traceSegment_026_3611_0017, g32p_row03_traceSegment_026_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 3577 68 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3577 34 34, g32p_row03_traceSegment_026_3577_0034, g32p_row03_traceSegment_026_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 3510 135 = [0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3510 67 68, g32p_row03_traceSegment_026_3510_0067, g32p_row03_traceSegment_026_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 3645 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3669 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3661 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3661 8 9, g32p_row03_traceSegment_026_3661_0008, g32p_row03_traceSegment_026_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 3645 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3645 16 17, g32p_row03_traceSegment_026_3645_0016, g32p_row03_traceSegment_026_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3686 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3678 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3678 8 9, g32p_row03_traceSegment_026_3678_0008, g32p_row03_traceSegment_026_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3695 8 9, g32p_row03_traceSegment_026_3695_0008, g32p_row03_traceSegment_026_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3678 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3678 17 17, g32p_row03_traceSegment_026_3678_0017, g32p_row03_traceSegment_026_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 3645 67 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3645 33 34, g32p_row03_traceSegment_026_3645_0033, g32p_row03_traceSegment_026_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3720 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3712 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3712 8 9, g32p_row03_traceSegment_026_3712_0008, g32p_row03_traceSegment_026_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3729 8 9, g32p_row03_traceSegment_026_3729_0008, g32p_row03_traceSegment_026_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3712 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3712 17 17, g32p_row03_traceSegment_026_3712_0017, g32p_row03_traceSegment_026_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3746 8 9, g32p_row03_traceSegment_026_3746_0008, g32p_row03_traceSegment_026_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3763 8 9, g32p_row03_traceSegment_026_3763_0008, g32p_row03_traceSegment_026_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3746 17 17, g32p_row03_traceSegment_026_3746_0017, g32p_row03_traceSegment_026_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 3712 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3712 34 34, g32p_row03_traceSegment_026_3712_0034, g32p_row03_traceSegment_026_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 3645 135 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3645 67 68, g32p_row03_traceSegment_026_3645_0067, g32p_row03_traceSegment_026_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 3510 270 = [0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3510 135 135, g32p_row03_traceSegment_026_3510_0135, g32p_row03_traceSegment_026_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_026 3240 540 = [0, 0, 42] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3240 270 270, g32p_row03_traceSegment_026_3240_0270, g32p_row03_traceSegment_026_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3796 8 9, g32p_row03_traceSegment_026_3796_0008, g32p_row03_traceSegment_026_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3780 16 17, g32p_row03_traceSegment_026_3780_0016, g32p_row03_traceSegment_026_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3813 8 9, g32p_row03_traceSegment_026_3813_0008, g32p_row03_traceSegment_026_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3830 8 9, g32p_row03_traceSegment_026_3830_0008, g32p_row03_traceSegment_026_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3813 17 17, g32p_row03_traceSegment_026_3813_0017, g32p_row03_traceSegment_026_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3780 33 34, g32p_row03_traceSegment_026_3780_0033, g32p_row03_traceSegment_026_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3847 8 9, g32p_row03_traceSegment_026_3847_0008, g32p_row03_traceSegment_026_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3864 8 9, g32p_row03_traceSegment_026_3864_0008, g32p_row03_traceSegment_026_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3847 17 17, g32p_row03_traceSegment_026_3847_0017, g32p_row03_traceSegment_026_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3881 8 9, g32p_row03_traceSegment_026_3881_0008, g32p_row03_traceSegment_026_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3898 8 9, g32p_row03_traceSegment_026_3898_0008, g32p_row03_traceSegment_026_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3881 17 17, g32p_row03_traceSegment_026_3881_0017, g32p_row03_traceSegment_026_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3847 34 34, g32p_row03_traceSegment_026_3847_0034, g32p_row03_traceSegment_026_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 3780 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3780 67 68, g32p_row03_traceSegment_026_3780_0067, g32p_row03_traceSegment_026_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3931 8 9, g32p_row03_traceSegment_026_3931_0008, g32p_row03_traceSegment_026_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3915 16 17, g32p_row03_traceSegment_026_3915_0016, g32p_row03_traceSegment_026_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3948 8 9, g32p_row03_traceSegment_026_3948_0008, g32p_row03_traceSegment_026_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3973 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3965 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3965 8 9, g32p_row03_traceSegment_026_3965_0008, g32p_row03_traceSegment_026_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3948 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3948 17 17, g32p_row03_traceSegment_026_3948_0017, g32p_row03_traceSegment_026_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 3915 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3915 33 34, g32p_row03_traceSegment_026_3915_0033, g32p_row03_traceSegment_026_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3982 8 9, g32p_row03_traceSegment_026_3982_0008, g32p_row03_traceSegment_026_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3999 8 9, g32p_row03_traceSegment_026_3999_0008, g32p_row03_traceSegment_026_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3982 17 17, g32p_row03_traceSegment_026_3982_0017, g32p_row03_traceSegment_026_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4016 8 9, g32p_row03_traceSegment_026_4016_0008, g32p_row03_traceSegment_026_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4033 8 9, g32p_row03_traceSegment_026_4033_0008, g32p_row03_traceSegment_026_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4016 17 17, g32p_row03_traceSegment_026_4016_0017, g32p_row03_traceSegment_026_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3982 34 34, g32p_row03_traceSegment_026_3982_0034, g32p_row03_traceSegment_026_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 3915 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3915 67 68, g32p_row03_traceSegment_026_3915_0067, g32p_row03_traceSegment_026_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 3780 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3780 135 135, g32p_row03_traceSegment_026_3780_0135, g32p_row03_traceSegment_026_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4066 8 9, g32p_row03_traceSegment_026_4066_0008, g32p_row03_traceSegment_026_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4050 16 17, g32p_row03_traceSegment_026_4050_0016, g32p_row03_traceSegment_026_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4083 8 9, g32p_row03_traceSegment_026_4083_0008, g32p_row03_traceSegment_026_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4100 8 9, g32p_row03_traceSegment_026_4100_0008, g32p_row03_traceSegment_026_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4083 17 17, g32p_row03_traceSegment_026_4083_0017, g32p_row03_traceSegment_026_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4050 33 34, g32p_row03_traceSegment_026_4050_0033, g32p_row03_traceSegment_026_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4117 8 9, g32p_row03_traceSegment_026_4117_0008, g32p_row03_traceSegment_026_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4134 8 9, g32p_row03_traceSegment_026_4134_0008, g32p_row03_traceSegment_026_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4117 17 17, g32p_row03_traceSegment_026_4117_0017, g32p_row03_traceSegment_026_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4151 8 9, g32p_row03_traceSegment_026_4151_0008, g32p_row03_traceSegment_026_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4168 8 9, g32p_row03_traceSegment_026_4168_0008, g32p_row03_traceSegment_026_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4151 17 17, g32p_row03_traceSegment_026_4151_0017, g32p_row03_traceSegment_026_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4117 34 34, g32p_row03_traceSegment_026_4117_0034, g32p_row03_traceSegment_026_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 4050 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4050 67 68, g32p_row03_traceSegment_026_4050_0067, g32p_row03_traceSegment_026_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_026 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4209 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4201 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4201 8 9, g32p_row03_traceSegment_026_4201_0008, g32p_row03_traceSegment_026_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_026 4185 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4185 16 17, g32p_row03_traceSegment_026_4185_0016, g32p_row03_traceSegment_026_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4218 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4226 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4218 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4218 8 9, g32p_row03_traceSegment_026_4218_0008, g32p_row03_traceSegment_026_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4235 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4235 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4235 8 9, g32p_row03_traceSegment_026_4235_0008, g32p_row03_traceSegment_026_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 4218 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4218 17 17, g32p_row03_traceSegment_026_4218_0017, g32p_row03_traceSegment_026_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_026 4185 67 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4185 33 34, g32p_row03_traceSegment_026_4185_0033, g32p_row03_traceSegment_026_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4252 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4252 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4252 8 9, g32p_row03_traceSegment_026_4252_0008, g32p_row03_traceSegment_026_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4269 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4269 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4269 8 9, g32p_row03_traceSegment_026_4269_0008, g32p_row03_traceSegment_026_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 4252 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4252 17 17, g32p_row03_traceSegment_026_4252_0017, g32p_row03_traceSegment_026_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4294 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4286 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4286 8 9, g32p_row03_traceSegment_026_4286_0008, g32p_row03_traceSegment_026_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_026 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_026 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_026_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_026 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4303 8 9, g32p_row03_traceSegment_026_4303_0008, g32p_row03_traceSegment_026_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_026 4286 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4286 17 17, g32p_row03_traceSegment_026_4286_0017, g32p_row03_traceSegment_026_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_026 4252 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4252 34 34, g32p_row03_traceSegment_026_4252_0034, g32p_row03_traceSegment_026_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_026 4185 135 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4185 67 68, g32p_row03_traceSegment_026_4185_0067, g32p_row03_traceSegment_026_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_026_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_026 4050 270 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 4050 135 135, g32p_row03_traceSegment_026_4050_0135, g32p_row03_traceSegment_026_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_026 3780 540 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3780 270 270, g32p_row03_traceSegment_026_3780_0270, g32p_row03_traceSegment_026_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_026_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_026 3240 1080 = [0, 0, 50] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 3240 540 540, g32p_row03_traceSegment_026_3240_0540, g32p_row03_traceSegment_026_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_026_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_026 2160 2160 = [0, 0, 71] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 2160 1080 1080, g32p_row03_traceSegment_026_2160_1080, g32p_row03_traceSegment_026_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_026_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_026 0 4320 = [0, 0, 144] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_026 0 2160 2160, g32p_row03_traceSegment_026_0000_2160, g32p_row03_traceSegment_026_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_026 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 26 = [0, 0, 144] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_026_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_030 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 30 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_030_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 0 16 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 16 8 9, g32p_row03_traceSegment_030_0016_0008, g32p_row03_traceSegment_030_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 0 33 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 0 16 17, g32p_row03_traceSegment_030_0000_0016, g32p_row03_traceSegment_030_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 33 8 = [0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 41 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 33 17 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 33 8 9, g32p_row03_traceSegment_030_0033_0008, g32p_row03_traceSegment_030_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 50 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 50 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 50 8 9, g32p_row03_traceSegment_030_0050_0008, g32p_row03_traceSegment_030_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 33 34 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 33 17 17, g32p_row03_traceSegment_030_0033_0017, g32p_row03_traceSegment_030_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 0 67 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 0 33 34, g32p_row03_traceSegment_030_0000_0033, g32p_row03_traceSegment_030_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 67 8 9, g32p_row03_traceSegment_030_0067_0008, g32p_row03_traceSegment_030_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 84 8 9, g32p_row03_traceSegment_030_0084_0008, g32p_row03_traceSegment_030_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 67 17 17, g32p_row03_traceSegment_030_0067_0017, g32p_row03_traceSegment_030_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 101 8 9, g32p_row03_traceSegment_030_0101_0008, g32p_row03_traceSegment_030_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 118 8 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 126 9 = [0, 5] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 118 17 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 118 8 9, g32p_row03_traceSegment_030_0118_0008, g32p_row03_traceSegment_030_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 101 34 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 101 17 17, g32p_row03_traceSegment_030_0101_0017, g32p_row03_traceSegment_030_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 67 68 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 67 34 34, g32p_row03_traceSegment_030_0067_0034, g32p_row03_traceSegment_030_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 0 135 = [0, 21] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 0 67 68, g32p_row03_traceSegment_030_0000_0067, g32p_row03_traceSegment_030_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 135 16 = [0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 151 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 151 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 151 8 9, g32p_row03_traceSegment_030_0151_0008, g32p_row03_traceSegment_030_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 135 33 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 135 16 17, g32p_row03_traceSegment_030_0135_0016, g32p_row03_traceSegment_030_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 168 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 176 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 168 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 168 8 9, g32p_row03_traceSegment_030_0168_0008, g32p_row03_traceSegment_030_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 185 8 9, g32p_row03_traceSegment_030_0185_0008, g32p_row03_traceSegment_030_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 168 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 168 17 17, g32p_row03_traceSegment_030_0168_0017, g32p_row03_traceSegment_030_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 135 67 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 135 33 34, g32p_row03_traceSegment_030_0135_0033, g32p_row03_traceSegment_030_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 202 8 9, g32p_row03_traceSegment_030_0202_0008, g32p_row03_traceSegment_030_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 219 8 9, g32p_row03_traceSegment_030_0219_0008, g32p_row03_traceSegment_030_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 202 17 17, g32p_row03_traceSegment_030_0202_0017, g32p_row03_traceSegment_030_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 236 8 9, g32p_row03_traceSegment_030_0236_0008, g32p_row03_traceSegment_030_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 253 8 9, g32p_row03_traceSegment_030_0253_0008, g32p_row03_traceSegment_030_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 236 17 17, g32p_row03_traceSegment_030_0236_0017, g32p_row03_traceSegment_030_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 202 34 34, g32p_row03_traceSegment_030_0202_0034, g32p_row03_traceSegment_030_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 135 135 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 135 67 68, g32p_row03_traceSegment_030_0135_0067, g32p_row03_traceSegment_030_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 0 270 = [0, 28] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 0 135 135, g32p_row03_traceSegment_030_0000_0135, g32p_row03_traceSegment_030_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 286 8 9, g32p_row03_traceSegment_030_0286_0008, g32p_row03_traceSegment_030_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 270 16 17, g32p_row03_traceSegment_030_0270_0016, g32p_row03_traceSegment_030_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 303 8 9, g32p_row03_traceSegment_030_0303_0008, g32p_row03_traceSegment_030_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 320 8 9, g32p_row03_traceSegment_030_0320_0008, g32p_row03_traceSegment_030_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 303 17 17, g32p_row03_traceSegment_030_0303_0017, g32p_row03_traceSegment_030_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 270 33 34, g32p_row03_traceSegment_030_0270_0033, g32p_row03_traceSegment_030_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 337 8 9, g32p_row03_traceSegment_030_0337_0008, g32p_row03_traceSegment_030_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 354 8 9, g32p_row03_traceSegment_030_0354_0008, g32p_row03_traceSegment_030_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 337 17 17, g32p_row03_traceSegment_030_0337_0017, g32p_row03_traceSegment_030_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 371 8 9, g32p_row03_traceSegment_030_0371_0008, g32p_row03_traceSegment_030_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 396 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 388 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 388 8 9, g32p_row03_traceSegment_030_0388_0008, g32p_row03_traceSegment_030_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 371 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 371 17 17, g32p_row03_traceSegment_030_0371_0017, g32p_row03_traceSegment_030_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 337 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 337 34 34, g32p_row03_traceSegment_030_0337_0034, g32p_row03_traceSegment_030_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 270 135 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 270 67 68, g32p_row03_traceSegment_030_0270_0067, g32p_row03_traceSegment_030_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 405 16 = [0, 8] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 421 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 429 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 421 17 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 421 8 9, g32p_row03_traceSegment_030_0421_0008, g32p_row03_traceSegment_030_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 405 33 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 405 16 17, g32p_row03_traceSegment_030_0405_0016, g32p_row03_traceSegment_030_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 438 8 9, g32p_row03_traceSegment_030_0438_0008, g32p_row03_traceSegment_030_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 455 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 455 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 455 8 9, g32p_row03_traceSegment_030_0455_0008, g32p_row03_traceSegment_030_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 438 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 438 17 17, g32p_row03_traceSegment_030_0438_0017, g32p_row03_traceSegment_030_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 405 67 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 405 33 34, g32p_row03_traceSegment_030_0405_0033, g32p_row03_traceSegment_030_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 472 8 9, g32p_row03_traceSegment_030_0472_0008, g32p_row03_traceSegment_030_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 497 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 489 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 489 8 9, g32p_row03_traceSegment_030_0489_0008, g32p_row03_traceSegment_030_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 472 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 472 17 17, g32p_row03_traceSegment_030_0472_0017, g32p_row03_traceSegment_030_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 506 8 9, g32p_row03_traceSegment_030_0506_0008, g32p_row03_traceSegment_030_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 523 8 9, g32p_row03_traceSegment_030_0523_0008, g32p_row03_traceSegment_030_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 506 17 17, g32p_row03_traceSegment_030_0506_0017, g32p_row03_traceSegment_030_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 472 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 472 34 34, g32p_row03_traceSegment_030_0472_0034, g32p_row03_traceSegment_030_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 405 135 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 405 67 68, g32p_row03_traceSegment_030_0405_0067, g32p_row03_traceSegment_030_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 270 270 = [0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 270 135 135, g32p_row03_traceSegment_030_0270_0135, g32p_row03_traceSegment_030_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_030 0 540 = [0, 44] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 0 270 270, g32p_row03_traceSegment_030_0000_0270, g32p_row03_traceSegment_030_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 556 8 9, g32p_row03_traceSegment_030_0556_0008, g32p_row03_traceSegment_030_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 540 16 17, g32p_row03_traceSegment_030_0540_0016, g32p_row03_traceSegment_030_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 573 8 9, g32p_row03_traceSegment_030_0573_0008, g32p_row03_traceSegment_030_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 590 8 9, g32p_row03_traceSegment_030_0590_0008, g32p_row03_traceSegment_030_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 573 17 17, g32p_row03_traceSegment_030_0573_0017, g32p_row03_traceSegment_030_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 540 33 34, g32p_row03_traceSegment_030_0540_0033, g32p_row03_traceSegment_030_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 607 8 9, g32p_row03_traceSegment_030_0607_0008, g32p_row03_traceSegment_030_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 624 8 9, g32p_row03_traceSegment_030_0624_0008, g32p_row03_traceSegment_030_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 607 17 17, g32p_row03_traceSegment_030_0607_0017, g32p_row03_traceSegment_030_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 641 8 9, g32p_row03_traceSegment_030_0641_0008, g32p_row03_traceSegment_030_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 658 8 9, g32p_row03_traceSegment_030_0658_0008, g32p_row03_traceSegment_030_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 641 17 17, g32p_row03_traceSegment_030_0641_0017, g32p_row03_traceSegment_030_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 607 34 34, g32p_row03_traceSegment_030_0607_0034, g32p_row03_traceSegment_030_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 540 67 68, g32p_row03_traceSegment_030_0540_0067, g32p_row03_traceSegment_030_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 691 8 9, g32p_row03_traceSegment_030_0691_0008, g32p_row03_traceSegment_030_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 675 16 17, g32p_row03_traceSegment_030_0675_0016, g32p_row03_traceSegment_030_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 708 8 9, g32p_row03_traceSegment_030_0708_0008, g32p_row03_traceSegment_030_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 725 8 9, g32p_row03_traceSegment_030_0725_0008, g32p_row03_traceSegment_030_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 708 17 17, g32p_row03_traceSegment_030_0708_0017, g32p_row03_traceSegment_030_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 675 33 34, g32p_row03_traceSegment_030_0675_0033, g32p_row03_traceSegment_030_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 742 8 9, g32p_row03_traceSegment_030_0742_0008, g32p_row03_traceSegment_030_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 759 8 9, g32p_row03_traceSegment_030_0759_0008, g32p_row03_traceSegment_030_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 742 17 17, g32p_row03_traceSegment_030_0742_0017, g32p_row03_traceSegment_030_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 776 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 776 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 776 8 9, g32p_row03_traceSegment_030_0776_0008, g32p_row03_traceSegment_030_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 793 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 801 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 793 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 793 8 9, g32p_row03_traceSegment_030_0793_0008, g32p_row03_traceSegment_030_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 776 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 776 17 17, g32p_row03_traceSegment_030_0776_0017, g32p_row03_traceSegment_030_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 742 68 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 742 34 34, g32p_row03_traceSegment_030_0742_0034, g32p_row03_traceSegment_030_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 675 135 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 675 67 68, g32p_row03_traceSegment_030_0675_0067, g32p_row03_traceSegment_030_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 540 270 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 540 135 135, g32p_row03_traceSegment_030_0540_0135, g32p_row03_traceSegment_030_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 810 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 826 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 834 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 826 17 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 826 8 9, g32p_row03_traceSegment_030_0826_0008, g32p_row03_traceSegment_030_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 810 33 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 810 16 17, g32p_row03_traceSegment_030_0810_0016, g32p_row03_traceSegment_030_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 843 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 851 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 843 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 843 8 9, g32p_row03_traceSegment_030_0843_0008, g32p_row03_traceSegment_030_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 868 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 860 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 860 8 9, g32p_row03_traceSegment_030_0860_0008, g32p_row03_traceSegment_030_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 843 34 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 843 17 17, g32p_row03_traceSegment_030_0843_0017, g32p_row03_traceSegment_030_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 810 67 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 810 33 34, g32p_row03_traceSegment_030_0810_0033, g32p_row03_traceSegment_030_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 877 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 877 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 877 8 9, g32p_row03_traceSegment_030_0877_0008, g32p_row03_traceSegment_030_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 894 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 902 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 894 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 894 8 9, g32p_row03_traceSegment_030_0894_0008, g32p_row03_traceSegment_030_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 877 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 877 17 17, g32p_row03_traceSegment_030_0877_0017, g32p_row03_traceSegment_030_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 911 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 919 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 911 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 911 8 9, g32p_row03_traceSegment_030_0911_0008, g32p_row03_traceSegment_030_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 928 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 936 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 928 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 928 8 9, g32p_row03_traceSegment_030_0928_0008, g32p_row03_traceSegment_030_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 911 34 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 911 17 17, g32p_row03_traceSegment_030_0911_0017, g32p_row03_traceSegment_030_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 877 68 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 877 34 34, g32p_row03_traceSegment_030_0877_0034, g32p_row03_traceSegment_030_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 810 135 = [0, 21] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 810 67 68, g32p_row03_traceSegment_030_0810_0067, g32p_row03_traceSegment_030_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 945 16 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 961 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 969 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 961 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 961 8 9, g32p_row03_traceSegment_030_0961_0008, g32p_row03_traceSegment_030_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 945 33 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 945 16 17, g32p_row03_traceSegment_030_0945_0016, g32p_row03_traceSegment_030_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 978 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 986 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 978 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 978 8 9, g32p_row03_traceSegment_030_0978_0008, g32p_row03_traceSegment_030_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 995 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1003 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 995 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 995 8 9, g32p_row03_traceSegment_030_0995_0008, g32p_row03_traceSegment_030_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 978 34 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 978 17 17, g32p_row03_traceSegment_030_0978_0017, g32p_row03_traceSegment_030_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 945 67 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 945 33 34, g32p_row03_traceSegment_030_0945_0033, g32p_row03_traceSegment_030_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1020 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1012 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1012 8 9, g32p_row03_traceSegment_030_1012_0008, g32p_row03_traceSegment_030_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1029 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1037 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1029 17 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1029 8 9, g32p_row03_traceSegment_030_1029_0008, g32p_row03_traceSegment_030_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1012 34 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1012 17 17, g32p_row03_traceSegment_030_1012_0017, g32p_row03_traceSegment_030_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1046 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1046 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1046 8 9, g32p_row03_traceSegment_030_1046_0008, g32p_row03_traceSegment_030_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1063 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1071 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1063 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1063 8 9, g32p_row03_traceSegment_030_1063_0008, g32p_row03_traceSegment_030_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1046 34 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1046 17 17, g32p_row03_traceSegment_030_1046_0017, g32p_row03_traceSegment_030_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 1012 68 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1012 34 34, g32p_row03_traceSegment_030_1012_0034, g32p_row03_traceSegment_030_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 945 135 = [0, 20] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 945 67 68, g32p_row03_traceSegment_030_0945_0067, g32p_row03_traceSegment_030_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 810 270 = [0, 41] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 810 135 135, g32p_row03_traceSegment_030_0810_0135, g32p_row03_traceSegment_030_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_030 540 540 = [0, 45] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 540 270 270, g32p_row03_traceSegment_030_0540_0270, g32p_row03_traceSegment_030_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_030 0 1080 = [0, 89] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 0 540 540, g32p_row03_traceSegment_030_0000_0540, g32p_row03_traceSegment_030_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 1080 16 = [0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1104 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1096 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1096 8 9, g32p_row03_traceSegment_030_1096_0008, g32p_row03_traceSegment_030_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 1080 33 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1080 16 17, g32p_row03_traceSegment_030_1080_0016, g32p_row03_traceSegment_030_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1113 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1121 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1113 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1113 8 9, g32p_row03_traceSegment_030_1113_0008, g32p_row03_traceSegment_030_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1130 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1138 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1130 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1130 8 9, g32p_row03_traceSegment_030_1130_0008, g32p_row03_traceSegment_030_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1113 34 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1113 17 17, g32p_row03_traceSegment_030_1113_0017, g32p_row03_traceSegment_030_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 1080 67 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1080 33 34, g32p_row03_traceSegment_030_1080_0033, g32p_row03_traceSegment_030_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1147 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1155 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1147 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1147 8 9, g32p_row03_traceSegment_030_1147_0008, g32p_row03_traceSegment_030_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1164 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1172 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1164 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1164 8 9, g32p_row03_traceSegment_030_1164_0008, g32p_row03_traceSegment_030_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1147 34 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1147 17 17, g32p_row03_traceSegment_030_1147_0017, g32p_row03_traceSegment_030_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1181 8 9, g32p_row03_traceSegment_030_1181_0008, g32p_row03_traceSegment_030_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1206 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1198 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1198 8 9, g32p_row03_traceSegment_030_1198_0008, g32p_row03_traceSegment_030_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1181 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1181 17 17, g32p_row03_traceSegment_030_1181_0017, g32p_row03_traceSegment_030_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 1147 68 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1147 34 34, g32p_row03_traceSegment_030_1147_0034, g32p_row03_traceSegment_030_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 1080 135 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1080 67 68, g32p_row03_traceSegment_030_1080_0067, g32p_row03_traceSegment_030_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 1215 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1239 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1231 17 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1231 8 9, g32p_row03_traceSegment_030_1231_0008, g32p_row03_traceSegment_030_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 1215 33 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1215 16 17, g32p_row03_traceSegment_030_1215_0016, g32p_row03_traceSegment_030_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1248 8 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1256 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1248 17 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1248 8 9, g32p_row03_traceSegment_030_1248_0008, g32p_row03_traceSegment_030_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1265 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1273 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1265 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1265 8 9, g32p_row03_traceSegment_030_1265_0008, g32p_row03_traceSegment_030_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1248 34 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1248 17 17, g32p_row03_traceSegment_030_1248_0017, g32p_row03_traceSegment_030_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 1215 67 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1215 33 34, g32p_row03_traceSegment_030_1215_0033, g32p_row03_traceSegment_030_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1282 8 9, g32p_row03_traceSegment_030_1282_0008, g32p_row03_traceSegment_030_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1299 8 9, g32p_row03_traceSegment_030_1299_0008, g32p_row03_traceSegment_030_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1282 17 17, g32p_row03_traceSegment_030_1282_0017, g32p_row03_traceSegment_030_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1316 8 9, g32p_row03_traceSegment_030_1316_0008, g32p_row03_traceSegment_030_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1333 8 9, g32p_row03_traceSegment_030_1333_0008, g32p_row03_traceSegment_030_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1316 17 17, g32p_row03_traceSegment_030_1316_0017, g32p_row03_traceSegment_030_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1282 34 34, g32p_row03_traceSegment_030_1282_0034, g32p_row03_traceSegment_030_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 1215 135 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1215 67 68, g32p_row03_traceSegment_030_1215_0067, g32p_row03_traceSegment_030_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 1080 270 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1080 135 135, g32p_row03_traceSegment_030_1080_0135, g32p_row03_traceSegment_030_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1366 8 9, g32p_row03_traceSegment_030_1366_0008, g32p_row03_traceSegment_030_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1350 16 17, g32p_row03_traceSegment_030_1350_0016, g32p_row03_traceSegment_030_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1383 8 9, g32p_row03_traceSegment_030_1383_0008, g32p_row03_traceSegment_030_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1400 8 9, g32p_row03_traceSegment_030_1400_0008, g32p_row03_traceSegment_030_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1383 17 17, g32p_row03_traceSegment_030_1383_0017, g32p_row03_traceSegment_030_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1350 33 34, g32p_row03_traceSegment_030_1350_0033, g32p_row03_traceSegment_030_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1417 8 9, g32p_row03_traceSegment_030_1417_0008, g32p_row03_traceSegment_030_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1434 8 9, g32p_row03_traceSegment_030_1434_0008, g32p_row03_traceSegment_030_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1417 17 17, g32p_row03_traceSegment_030_1417_0017, g32p_row03_traceSegment_030_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1451 8 9, g32p_row03_traceSegment_030_1451_0008, g32p_row03_traceSegment_030_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1468 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1468 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1468 8 9, g32p_row03_traceSegment_030_1468_0008, g32p_row03_traceSegment_030_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1451 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1451 17 17, g32p_row03_traceSegment_030_1451_0017, g32p_row03_traceSegment_030_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 1417 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1417 34 34, g32p_row03_traceSegment_030_1417_0034, g32p_row03_traceSegment_030_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 1350 135 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1350 67 68, g32p_row03_traceSegment_030_1350_0067, g32p_row03_traceSegment_030_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1501 8 9, g32p_row03_traceSegment_030_1501_0008, g32p_row03_traceSegment_030_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1485 16 17, g32p_row03_traceSegment_030_1485_0016, g32p_row03_traceSegment_030_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1518 8 9, g32p_row03_traceSegment_030_1518_0008, g32p_row03_traceSegment_030_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1535 8 9, g32p_row03_traceSegment_030_1535_0008, g32p_row03_traceSegment_030_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1518 17 17, g32p_row03_traceSegment_030_1518_0017, g32p_row03_traceSegment_030_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1485 33 34, g32p_row03_traceSegment_030_1485_0033, g32p_row03_traceSegment_030_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1552 8 9, g32p_row03_traceSegment_030_1552_0008, g32p_row03_traceSegment_030_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1569 8 9, g32p_row03_traceSegment_030_1569_0008, g32p_row03_traceSegment_030_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1552 17 17, g32p_row03_traceSegment_030_1552_0017, g32p_row03_traceSegment_030_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1586 8 9, g32p_row03_traceSegment_030_1586_0008, g32p_row03_traceSegment_030_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1603 8 9, g32p_row03_traceSegment_030_1603_0008, g32p_row03_traceSegment_030_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1586 17 17, g32p_row03_traceSegment_030_1586_0017, g32p_row03_traceSegment_030_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1552 34 34, g32p_row03_traceSegment_030_1552_0034, g32p_row03_traceSegment_030_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 1485 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1485 67 68, g32p_row03_traceSegment_030_1485_0067, g32p_row03_traceSegment_030_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 1350 270 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1350 135 135, g32p_row03_traceSegment_030_1350_0135, g32p_row03_traceSegment_030_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_030 1080 540 = [0, 32] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1080 270 270, g32p_row03_traceSegment_030_1080_0270, g32p_row03_traceSegment_030_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1644 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1636 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1636 8 9, g32p_row03_traceSegment_030_1636_0008, g32p_row03_traceSegment_030_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 1620 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1620 16 17, g32p_row03_traceSegment_030_1620_0016, g32p_row03_traceSegment_030_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1653 8 9, g32p_row03_traceSegment_030_1653_0008, g32p_row03_traceSegment_030_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1670 8 9, g32p_row03_traceSegment_030_1670_0008, g32p_row03_traceSegment_030_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1653 17 17, g32p_row03_traceSegment_030_1653_0017, g32p_row03_traceSegment_030_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 1620 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1620 33 34, g32p_row03_traceSegment_030_1620_0033, g32p_row03_traceSegment_030_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1687 8 9, g32p_row03_traceSegment_030_1687_0008, g32p_row03_traceSegment_030_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1704 8 9, g32p_row03_traceSegment_030_1704_0008, g32p_row03_traceSegment_030_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1687 17 17, g32p_row03_traceSegment_030_1687_0017, g32p_row03_traceSegment_030_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1721 8 9, g32p_row03_traceSegment_030_1721_0008, g32p_row03_traceSegment_030_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1746 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1738 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1738 8 9, g32p_row03_traceSegment_030_1738_0008, g32p_row03_traceSegment_030_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1721 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1721 17 17, g32p_row03_traceSegment_030_1721_0017, g32p_row03_traceSegment_030_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 1687 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1687 34 34, g32p_row03_traceSegment_030_1687_0034, g32p_row03_traceSegment_030_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 1620 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1620 67 68, g32p_row03_traceSegment_030_1620_0067, g32p_row03_traceSegment_030_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1771 8 9, g32p_row03_traceSegment_030_1771_0008, g32p_row03_traceSegment_030_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1755 16 17, g32p_row03_traceSegment_030_1755_0016, g32p_row03_traceSegment_030_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1788 8 9, g32p_row03_traceSegment_030_1788_0008, g32p_row03_traceSegment_030_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1805 8 9, g32p_row03_traceSegment_030_1805_0008, g32p_row03_traceSegment_030_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1788 17 17, g32p_row03_traceSegment_030_1788_0017, g32p_row03_traceSegment_030_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1755 33 34, g32p_row03_traceSegment_030_1755_0033, g32p_row03_traceSegment_030_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1830 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1822 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1822 8 9, g32p_row03_traceSegment_030_1822_0008, g32p_row03_traceSegment_030_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1839 8 9, g32p_row03_traceSegment_030_1839_0008, g32p_row03_traceSegment_030_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1822 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1822 17 17, g32p_row03_traceSegment_030_1822_0017, g32p_row03_traceSegment_030_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1856 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1856 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1856 8 9, g32p_row03_traceSegment_030_1856_0008, g32p_row03_traceSegment_030_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1873 8 9, g32p_row03_traceSegment_030_1873_0008, g32p_row03_traceSegment_030_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1856 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1856 17 17, g32p_row03_traceSegment_030_1856_0017, g32p_row03_traceSegment_030_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 1822 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1822 34 34, g32p_row03_traceSegment_030_1822_0034, g32p_row03_traceSegment_030_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 1755 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1755 67 68, g32p_row03_traceSegment_030_1755_0067, g32p_row03_traceSegment_030_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 1620 270 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1620 135 135, g32p_row03_traceSegment_030_1620_0135, g32p_row03_traceSegment_030_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1906 8 9, g32p_row03_traceSegment_030_1906_0008, g32p_row03_traceSegment_030_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1890 16 17, g32p_row03_traceSegment_030_1890_0016, g32p_row03_traceSegment_030_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1923 8 9, g32p_row03_traceSegment_030_1923_0008, g32p_row03_traceSegment_030_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1940 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1940 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1940 8 9, g32p_row03_traceSegment_030_1940_0008, g32p_row03_traceSegment_030_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1923 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1923 17 17, g32p_row03_traceSegment_030_1923_0017, g32p_row03_traceSegment_030_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 1890 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1890 33 34, g32p_row03_traceSegment_030_1890_0033, g32p_row03_traceSegment_030_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1957 8 9, g32p_row03_traceSegment_030_1957_0008, g32p_row03_traceSegment_030_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1974 8 9, g32p_row03_traceSegment_030_1974_0008, g32p_row03_traceSegment_030_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1957 17 17, g32p_row03_traceSegment_030_1957_0017, g32p_row03_traceSegment_030_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 1999 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 1991 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1991 8 9, g32p_row03_traceSegment_030_1991_0008, g32p_row03_traceSegment_030_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2008 8 9, g32p_row03_traceSegment_030_2008_0008, g32p_row03_traceSegment_030_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 1991 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1991 17 17, g32p_row03_traceSegment_030_1991_0017, g32p_row03_traceSegment_030_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 1957 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1957 34 34, g32p_row03_traceSegment_030_1957_0034, g32p_row03_traceSegment_030_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 1890 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1890 67 68, g32p_row03_traceSegment_030_1890_0067, g32p_row03_traceSegment_030_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2041 8 9, g32p_row03_traceSegment_030_2041_0008, g32p_row03_traceSegment_030_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2025 16 17, g32p_row03_traceSegment_030_2025_0016, g32p_row03_traceSegment_030_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2058 8 9, g32p_row03_traceSegment_030_2058_0008, g32p_row03_traceSegment_030_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2075 8 9, g32p_row03_traceSegment_030_2075_0008, g32p_row03_traceSegment_030_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2058 17 17, g32p_row03_traceSegment_030_2058_0017, g32p_row03_traceSegment_030_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2025 33 34, g32p_row03_traceSegment_030_2025_0033, g32p_row03_traceSegment_030_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2092 8 9, g32p_row03_traceSegment_030_2092_0008, g32p_row03_traceSegment_030_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2117 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2109 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2109 8 9, g32p_row03_traceSegment_030_2109_0008, g32p_row03_traceSegment_030_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2092 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2092 17 17, g32p_row03_traceSegment_030_2092_0017, g32p_row03_traceSegment_030_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2134 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2126 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2126 8 9, g32p_row03_traceSegment_030_2126_0008, g32p_row03_traceSegment_030_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2143 8 9, g32p_row03_traceSegment_030_2143_0008, g32p_row03_traceSegment_030_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2126 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2126 17 17, g32p_row03_traceSegment_030_2126_0017, g32p_row03_traceSegment_030_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 2092 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2092 34 34, g32p_row03_traceSegment_030_2092_0034, g32p_row03_traceSegment_030_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 2025 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2025 67 68, g32p_row03_traceSegment_030_2025_0067, g32p_row03_traceSegment_030_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 1890 270 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1890 135 135, g32p_row03_traceSegment_030_1890_0135, g32p_row03_traceSegment_030_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_030 1620 540 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1620 270 270, g32p_row03_traceSegment_030_1620_0270, g32p_row03_traceSegment_030_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_030_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_030 1080 1080 = [0, 40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 1080 540 540, g32p_row03_traceSegment_030_1080_0540, g32p_row03_traceSegment_030_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_030 0 2160 = [0, 129] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 0 1080 1080, g32p_row03_traceSegment_030_0000_1080, g32p_row03_traceSegment_030_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2176 8 9, g32p_row03_traceSegment_030_2176_0008, g32p_row03_traceSegment_030_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2160 16 17, g32p_row03_traceSegment_030_2160_0016, g32p_row03_traceSegment_030_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2193 8 9, g32p_row03_traceSegment_030_2193_0008, g32p_row03_traceSegment_030_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2218 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2210 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2210 8 9, g32p_row03_traceSegment_030_2210_0008, g32p_row03_traceSegment_030_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2193 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2193 17 17, g32p_row03_traceSegment_030_2193_0017, g32p_row03_traceSegment_030_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 2160 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2160 33 34, g32p_row03_traceSegment_030_2160_0033, g32p_row03_traceSegment_030_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2235 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2227 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2227 8 9, g32p_row03_traceSegment_030_2227_0008, g32p_row03_traceSegment_030_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2244 8 9, g32p_row03_traceSegment_030_2244_0008, g32p_row03_traceSegment_030_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2227 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2227 17 17, g32p_row03_traceSegment_030_2227_0017, g32p_row03_traceSegment_030_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2261 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2261 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2261 8 9, g32p_row03_traceSegment_030_2261_0008, g32p_row03_traceSegment_030_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2278 8 9, g32p_row03_traceSegment_030_2278_0008, g32p_row03_traceSegment_030_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2261 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2261 17 17, g32p_row03_traceSegment_030_2261_0017, g32p_row03_traceSegment_030_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 2227 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2227 34 34, g32p_row03_traceSegment_030_2227_0034, g32p_row03_traceSegment_030_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 2160 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2160 67 68, g32p_row03_traceSegment_030_2160_0067, g32p_row03_traceSegment_030_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2311 8 9, g32p_row03_traceSegment_030_2311_0008, g32p_row03_traceSegment_030_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2295 16 17, g32p_row03_traceSegment_030_2295_0016, g32p_row03_traceSegment_030_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2328 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2336 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2328 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2328 8 9, g32p_row03_traceSegment_030_2328_0008, g32p_row03_traceSegment_030_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2353 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2345 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2345 8 9, g32p_row03_traceSegment_030_2345_0008, g32p_row03_traceSegment_030_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2328 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2328 17 17, g32p_row03_traceSegment_030_2328_0017, g32p_row03_traceSegment_030_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 2295 67 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2295 33 34, g32p_row03_traceSegment_030_2295_0033, g32p_row03_traceSegment_030_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2362 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2362 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2362 8 9, g32p_row03_traceSegment_030_2362_0008, g32p_row03_traceSegment_030_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2379 8 9, g32p_row03_traceSegment_030_2379_0008, g32p_row03_traceSegment_030_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2362 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2362 17 17, g32p_row03_traceSegment_030_2362_0017, g32p_row03_traceSegment_030_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2404 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2396 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2396 8 9, g32p_row03_traceSegment_030_2396_0008, g32p_row03_traceSegment_030_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2413 8 9, g32p_row03_traceSegment_030_2413_0008, g32p_row03_traceSegment_030_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2396 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2396 17 17, g32p_row03_traceSegment_030_2396_0017, g32p_row03_traceSegment_030_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 2362 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2362 34 34, g32p_row03_traceSegment_030_2362_0034, g32p_row03_traceSegment_030_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 2295 135 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2295 67 68, g32p_row03_traceSegment_030_2295_0067, g32p_row03_traceSegment_030_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 2160 270 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2160 135 135, g32p_row03_traceSegment_030_2160_0135, g32p_row03_traceSegment_030_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 2430 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2446 8 9, g32p_row03_traceSegment_030_2446_0008, g32p_row03_traceSegment_030_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 2430 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2430 16 17, g32p_row03_traceSegment_030_2430_0016, g32p_row03_traceSegment_030_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2463 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2471 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2463 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2463 8 9, g32p_row03_traceSegment_030_2463_0008, g32p_row03_traceSegment_030_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2480 8 9, g32p_row03_traceSegment_030_2480_0008, g32p_row03_traceSegment_030_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2463 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2463 17 17, g32p_row03_traceSegment_030_2463_0017, g32p_row03_traceSegment_030_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 2430 67 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2430 33 34, g32p_row03_traceSegment_030_2430_0033, g32p_row03_traceSegment_030_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2497 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2497 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2497 8 9, g32p_row03_traceSegment_030_2497_0008, g32p_row03_traceSegment_030_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2514 8 9, g32p_row03_traceSegment_030_2514_0008, g32p_row03_traceSegment_030_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2497 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2497 17 17, g32p_row03_traceSegment_030_2497_0017, g32p_row03_traceSegment_030_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2531 8 9, g32p_row03_traceSegment_030_2531_0008, g32p_row03_traceSegment_030_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2548 8 9, g32p_row03_traceSegment_030_2548_0008, g32p_row03_traceSegment_030_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2531 17 17, g32p_row03_traceSegment_030_2531_0017, g32p_row03_traceSegment_030_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 2497 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2497 34 34, g32p_row03_traceSegment_030_2497_0034, g32p_row03_traceSegment_030_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 2430 135 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2430 67 68, g32p_row03_traceSegment_030_2430_0067, g32p_row03_traceSegment_030_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 2565 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2581 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2589 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2581 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2581 8 9, g32p_row03_traceSegment_030_2581_0008, g32p_row03_traceSegment_030_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 2565 33 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2565 16 17, g32p_row03_traceSegment_030_2565_0016, g32p_row03_traceSegment_030_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2598 8 9, g32p_row03_traceSegment_030_2598_0008, g32p_row03_traceSegment_030_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2615 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2615 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2615 8 9, g32p_row03_traceSegment_030_2615_0008, g32p_row03_traceSegment_030_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2598 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2598 17 17, g32p_row03_traceSegment_030_2598_0017, g32p_row03_traceSegment_030_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 2565 67 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2565 33 34, g32p_row03_traceSegment_030_2565_0033, g32p_row03_traceSegment_030_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2632 8 9, g32p_row03_traceSegment_030_2632_0008, g32p_row03_traceSegment_030_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2649 8 9, g32p_row03_traceSegment_030_2649_0008, g32p_row03_traceSegment_030_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2632 17 17, g32p_row03_traceSegment_030_2632_0017, g32p_row03_traceSegment_030_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2666 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2674 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2666 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2666 8 9, g32p_row03_traceSegment_030_2666_0008, g32p_row03_traceSegment_030_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2683 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2683 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2683 8 9, g32p_row03_traceSegment_030_2683_0008, g32p_row03_traceSegment_030_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2666 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2666 17 17, g32p_row03_traceSegment_030_2666_0017, g32p_row03_traceSegment_030_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 2632 68 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2632 34 34, g32p_row03_traceSegment_030_2632_0034, g32p_row03_traceSegment_030_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 2565 135 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2565 67 68, g32p_row03_traceSegment_030_2565_0067, g32p_row03_traceSegment_030_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 2430 270 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2430 135 135, g32p_row03_traceSegment_030_2430_0135, g32p_row03_traceSegment_030_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_030 2160 540 = [0, 24] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2160 270 270, g32p_row03_traceSegment_030_2160_0270, g32p_row03_traceSegment_030_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2716 8 9, g32p_row03_traceSegment_030_2716_0008, g32p_row03_traceSegment_030_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2700 16 17, g32p_row03_traceSegment_030_2700_0016, g32p_row03_traceSegment_030_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2733 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2733 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2733 8 9, g32p_row03_traceSegment_030_2733_0008, g32p_row03_traceSegment_030_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2750 8 9, g32p_row03_traceSegment_030_2750_0008, g32p_row03_traceSegment_030_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2733 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2733 17 17, g32p_row03_traceSegment_030_2733_0017, g32p_row03_traceSegment_030_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 2700 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2700 33 34, g32p_row03_traceSegment_030_2700_0033, g32p_row03_traceSegment_030_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2767 8 9, g32p_row03_traceSegment_030_2767_0008, g32p_row03_traceSegment_030_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2784 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2784 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2784 8 9, g32p_row03_traceSegment_030_2784_0008, g32p_row03_traceSegment_030_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2767 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2767 17 17, g32p_row03_traceSegment_030_2767_0017, g32p_row03_traceSegment_030_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2801 8 9, g32p_row03_traceSegment_030_2801_0008, g32p_row03_traceSegment_030_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2826 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2818 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2818 8 9, g32p_row03_traceSegment_030_2818_0008, g32p_row03_traceSegment_030_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2801 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2801 17 17, g32p_row03_traceSegment_030_2801_0017, g32p_row03_traceSegment_030_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 2767 68 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2767 34 34, g32p_row03_traceSegment_030_2767_0034, g32p_row03_traceSegment_030_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 2700 135 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2700 67 68, g32p_row03_traceSegment_030_2700_0067, g32p_row03_traceSegment_030_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2851 8 9, g32p_row03_traceSegment_030_2851_0008, g32p_row03_traceSegment_030_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2835 16 17, g32p_row03_traceSegment_030_2835_0016, g32p_row03_traceSegment_030_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2868 8 9, g32p_row03_traceSegment_030_2868_0008, g32p_row03_traceSegment_030_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2885 8 9, g32p_row03_traceSegment_030_2885_0008, g32p_row03_traceSegment_030_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2868 17 17, g32p_row03_traceSegment_030_2868_0017, g32p_row03_traceSegment_030_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2835 33 34, g32p_row03_traceSegment_030_2835_0033, g32p_row03_traceSegment_030_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2902 8 9, g32p_row03_traceSegment_030_2902_0008, g32p_row03_traceSegment_030_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2919 8 9, g32p_row03_traceSegment_030_2919_0008, g32p_row03_traceSegment_030_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2902 17 17, g32p_row03_traceSegment_030_2902_0017, g32p_row03_traceSegment_030_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2936 8 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2936 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2936 8 9, g32p_row03_traceSegment_030_2936_0008, g32p_row03_traceSegment_030_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2953 8 9, g32p_row03_traceSegment_030_2953_0008, g32p_row03_traceSegment_030_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 2936 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2936 17 17, g32p_row03_traceSegment_030_2936_0017, g32p_row03_traceSegment_030_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 2902 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2902 34 34, g32p_row03_traceSegment_030_2902_0034, g32p_row03_traceSegment_030_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 2835 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2835 67 68, g32p_row03_traceSegment_030_2835_0067, g32p_row03_traceSegment_030_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 2700 270 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2700 135 135, g32p_row03_traceSegment_030_2700_0135, g32p_row03_traceSegment_030_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2986 8 9, g32p_row03_traceSegment_030_2986_0008, g32p_row03_traceSegment_030_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2970 16 17, g32p_row03_traceSegment_030_2970_0016, g32p_row03_traceSegment_030_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3003 8 9, g32p_row03_traceSegment_030_3003_0008, g32p_row03_traceSegment_030_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3020 8 9, g32p_row03_traceSegment_030_3020_0008, g32p_row03_traceSegment_030_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3003 17 17, g32p_row03_traceSegment_030_3003_0017, g32p_row03_traceSegment_030_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2970 33 34, g32p_row03_traceSegment_030_2970_0033, g32p_row03_traceSegment_030_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3037 8 9, g32p_row03_traceSegment_030_3037_0008, g32p_row03_traceSegment_030_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3054 8 9, g32p_row03_traceSegment_030_3054_0008, g32p_row03_traceSegment_030_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3037 17 17, g32p_row03_traceSegment_030_3037_0017, g32p_row03_traceSegment_030_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3071 8 9, g32p_row03_traceSegment_030_3071_0008, g32p_row03_traceSegment_030_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3088 8 9, g32p_row03_traceSegment_030_3088_0008, g32p_row03_traceSegment_030_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3071 17 17, g32p_row03_traceSegment_030_3071_0017, g32p_row03_traceSegment_030_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3037 34 34, g32p_row03_traceSegment_030_3037_0034, g32p_row03_traceSegment_030_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2970 67 68, g32p_row03_traceSegment_030_2970_0067, g32p_row03_traceSegment_030_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3121 8 9, g32p_row03_traceSegment_030_3121_0008, g32p_row03_traceSegment_030_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3105 16 17, g32p_row03_traceSegment_030_3105_0016, g32p_row03_traceSegment_030_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3138 8 9, g32p_row03_traceSegment_030_3138_0008, g32p_row03_traceSegment_030_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3163 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3155 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3155 8 9, g32p_row03_traceSegment_030_3155_0008, g32p_row03_traceSegment_030_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3138 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3138 17 17, g32p_row03_traceSegment_030_3138_0017, g32p_row03_traceSegment_030_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 3105 67 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3105 33 34, g32p_row03_traceSegment_030_3105_0033, g32p_row03_traceSegment_030_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3172 8 9, g32p_row03_traceSegment_030_3172_0008, g32p_row03_traceSegment_030_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3189 8 9, g32p_row03_traceSegment_030_3189_0008, g32p_row03_traceSegment_030_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3172 17 17, g32p_row03_traceSegment_030_3172_0017, g32p_row03_traceSegment_030_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3206 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3206 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3206 8 9, g32p_row03_traceSegment_030_3206_0008, g32p_row03_traceSegment_030_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3223 8 9, g32p_row03_traceSegment_030_3223_0008, g32p_row03_traceSegment_030_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3206 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3206 17 17, g32p_row03_traceSegment_030_3206_0017, g32p_row03_traceSegment_030_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 3172 68 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3172 34 34, g32p_row03_traceSegment_030_3172_0034, g32p_row03_traceSegment_030_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 3105 135 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3105 67 68, g32p_row03_traceSegment_030_3105_0067, g32p_row03_traceSegment_030_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 2970 270 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2970 135 135, g32p_row03_traceSegment_030_2970_0135, g32p_row03_traceSegment_030_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_030 2700 540 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2700 270 270, g32p_row03_traceSegment_030_2700_0270, g32p_row03_traceSegment_030_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_030 2160 1080 = [0, 35] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2160 540 540, g32p_row03_traceSegment_030_2160_0540, g32p_row03_traceSegment_030_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3256 8 9, g32p_row03_traceSegment_030_3256_0008, g32p_row03_traceSegment_030_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3240 16 17, g32p_row03_traceSegment_030_3240_0016, g32p_row03_traceSegment_030_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3273 8 9, g32p_row03_traceSegment_030_3273_0008, g32p_row03_traceSegment_030_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3290 8 9, g32p_row03_traceSegment_030_3290_0008, g32p_row03_traceSegment_030_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3273 17 17, g32p_row03_traceSegment_030_3273_0017, g32p_row03_traceSegment_030_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3240 33 34, g32p_row03_traceSegment_030_3240_0033, g32p_row03_traceSegment_030_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3307 8 9, g32p_row03_traceSegment_030_3307_0008, g32p_row03_traceSegment_030_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3332 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3324 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3324 8 9, g32p_row03_traceSegment_030_3324_0008, g32p_row03_traceSegment_030_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3307 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3307 17 17, g32p_row03_traceSegment_030_3307_0017, g32p_row03_traceSegment_030_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3349 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3341 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3341 8 9, g32p_row03_traceSegment_030_3341_0008, g32p_row03_traceSegment_030_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3366 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3358 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3358 8 9, g32p_row03_traceSegment_030_3358_0008, g32p_row03_traceSegment_030_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3341 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3341 17 17, g32p_row03_traceSegment_030_3341_0017, g32p_row03_traceSegment_030_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 3307 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3307 34 34, g32p_row03_traceSegment_030_3307_0034, g32p_row03_traceSegment_030_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 3240 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3240 67 68, g32p_row03_traceSegment_030_3240_0067, g32p_row03_traceSegment_030_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 3375 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3391 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3391 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3391 8 9, g32p_row03_traceSegment_030_3391_0008, g32p_row03_traceSegment_030_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 3375 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3375 16 17, g32p_row03_traceSegment_030_3375_0016, g32p_row03_traceSegment_030_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3408 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3408 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3408 8 9, g32p_row03_traceSegment_030_3408_0008, g32p_row03_traceSegment_030_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3433 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3425 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3425 8 9, g32p_row03_traceSegment_030_3425_0008, g32p_row03_traceSegment_030_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3408 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3408 17 17, g32p_row03_traceSegment_030_3408_0017, g32p_row03_traceSegment_030_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 3375 67 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3375 33 34, g32p_row03_traceSegment_030_3375_0033, g32p_row03_traceSegment_030_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3442 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3450 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3442 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3442 8 9, g32p_row03_traceSegment_030_3442_0008, g32p_row03_traceSegment_030_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3467 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3459 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3459 8 9, g32p_row03_traceSegment_030_3459_0008, g32p_row03_traceSegment_030_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3442 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3442 17 17, g32p_row03_traceSegment_030_3442_0017, g32p_row03_traceSegment_030_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3476 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3476 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3476 8 9, g32p_row03_traceSegment_030_3476_0008, g32p_row03_traceSegment_030_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3493 8 9, g32p_row03_traceSegment_030_3493_0008, g32p_row03_traceSegment_030_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3476 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3476 17 17, g32p_row03_traceSegment_030_3476_0017, g32p_row03_traceSegment_030_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 3442 68 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3442 34 34, g32p_row03_traceSegment_030_3442_0034, g32p_row03_traceSegment_030_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 3375 135 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3375 67 68, g32p_row03_traceSegment_030_3375_0067, g32p_row03_traceSegment_030_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 3240 270 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3240 135 135, g32p_row03_traceSegment_030_3240_0135, g32p_row03_traceSegment_030_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3526 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3526 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3526 8 9, g32p_row03_traceSegment_030_3526_0008, g32p_row03_traceSegment_030_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 3510 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3510 16 17, g32p_row03_traceSegment_030_3510_0016, g32p_row03_traceSegment_030_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3543 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3543 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3543 8 9, g32p_row03_traceSegment_030_3543_0008, g32p_row03_traceSegment_030_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3560 8 9, g32p_row03_traceSegment_030_3560_0008, g32p_row03_traceSegment_030_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3543 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3543 17 17, g32p_row03_traceSegment_030_3543_0017, g32p_row03_traceSegment_030_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 3510 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3510 33 34, g32p_row03_traceSegment_030_3510_0033, g32p_row03_traceSegment_030_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3577 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3577 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3577 8 9, g32p_row03_traceSegment_030_3577_0008, g32p_row03_traceSegment_030_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3602 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3594 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3594 8 9, g32p_row03_traceSegment_030_3594_0008, g32p_row03_traceSegment_030_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3577 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3577 17 17, g32p_row03_traceSegment_030_3577_0017, g32p_row03_traceSegment_030_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3611 8 9, g32p_row03_traceSegment_030_3611_0008, g32p_row03_traceSegment_030_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3628 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3636 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3628 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3628 8 9, g32p_row03_traceSegment_030_3628_0008, g32p_row03_traceSegment_030_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3611 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3611 17 17, g32p_row03_traceSegment_030_3611_0017, g32p_row03_traceSegment_030_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 3577 68 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3577 34 34, g32p_row03_traceSegment_030_3577_0034, g32p_row03_traceSegment_030_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 3510 135 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3510 67 68, g32p_row03_traceSegment_030_3510_0067, g32p_row03_traceSegment_030_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 3645 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3661 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3669 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3661 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3661 8 9, g32p_row03_traceSegment_030_3661_0008, g32p_row03_traceSegment_030_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 3645 33 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3645 16 17, g32p_row03_traceSegment_030_3645_0016, g32p_row03_traceSegment_030_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3678 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3678 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3678 8 9, g32p_row03_traceSegment_030_3678_0008, g32p_row03_traceSegment_030_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3695 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3703 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3695 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3695 8 9, g32p_row03_traceSegment_030_3695_0008, g32p_row03_traceSegment_030_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3678 34 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3678 17 17, g32p_row03_traceSegment_030_3678_0017, g32p_row03_traceSegment_030_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 3645 67 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3645 33 34, g32p_row03_traceSegment_030_3645_0033, g32p_row03_traceSegment_030_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3712 8 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3720 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3712 17 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3712 8 9, g32p_row03_traceSegment_030_3712_0008, g32p_row03_traceSegment_030_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3729 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3737 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3729 17 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3729 8 9, g32p_row03_traceSegment_030_3729_0008, g32p_row03_traceSegment_030_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3712 34 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3712 17 17, g32p_row03_traceSegment_030_3712_0017, g32p_row03_traceSegment_030_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3746 8 9, g32p_row03_traceSegment_030_3746_0008, g32p_row03_traceSegment_030_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3771 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3763 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3763 8 9, g32p_row03_traceSegment_030_3763_0008, g32p_row03_traceSegment_030_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3746 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3746 17 17, g32p_row03_traceSegment_030_3746_0017, g32p_row03_traceSegment_030_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 3712 68 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3712 34 34, g32p_row03_traceSegment_030_3712_0034, g32p_row03_traceSegment_030_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 3645 135 = [0, 17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3645 67 68, g32p_row03_traceSegment_030_3645_0067, g32p_row03_traceSegment_030_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 3510 270 = [0, 23] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3510 135 135, g32p_row03_traceSegment_030_3510_0135, g32p_row03_traceSegment_030_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_030 3240 540 = [0, 36] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3240 270 270, g32p_row03_traceSegment_030_3240_0270, g32p_row03_traceSegment_030_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 3780 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3804 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3796 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3796 8 9, g32p_row03_traceSegment_030_3796_0008, g32p_row03_traceSegment_030_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 3780 33 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3780 16 17, g32p_row03_traceSegment_030_3780_0016, g32p_row03_traceSegment_030_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3813 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3813 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3813 8 9, g32p_row03_traceSegment_030_3813_0008, g32p_row03_traceSegment_030_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3830 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3838 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3830 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3830 8 9, g32p_row03_traceSegment_030_3830_0008, g32p_row03_traceSegment_030_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3813 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3813 17 17, g32p_row03_traceSegment_030_3813_0017, g32p_row03_traceSegment_030_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 3780 67 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3780 33 34, g32p_row03_traceSegment_030_3780_0033, g32p_row03_traceSegment_030_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3847 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3847 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3847 8 9, g32p_row03_traceSegment_030_3847_0008, g32p_row03_traceSegment_030_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3864 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3872 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3864 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3864 8 9, g32p_row03_traceSegment_030_3864_0008, g32p_row03_traceSegment_030_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3847 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3847 17 17, g32p_row03_traceSegment_030_3847_0017, g32p_row03_traceSegment_030_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3881 8 9, g32p_row03_traceSegment_030_3881_0008, g32p_row03_traceSegment_030_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3898 8 9, g32p_row03_traceSegment_030_3898_0008, g32p_row03_traceSegment_030_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3881 17 17, g32p_row03_traceSegment_030_3881_0017, g32p_row03_traceSegment_030_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 3847 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3847 34 34, g32p_row03_traceSegment_030_3847_0034, g32p_row03_traceSegment_030_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 3780 135 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3780 67 68, g32p_row03_traceSegment_030_3780_0067, g32p_row03_traceSegment_030_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 3915 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3931 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3931 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3931 8 9, g32p_row03_traceSegment_030_3931_0008, g32p_row03_traceSegment_030_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 3915 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3915 16 17, g32p_row03_traceSegment_030_3915_0016, g32p_row03_traceSegment_030_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3948 8 9, g32p_row03_traceSegment_030_3948_0008, g32p_row03_traceSegment_030_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3965 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3965 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3965 8 9, g32p_row03_traceSegment_030_3965_0008, g32p_row03_traceSegment_030_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3948 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3948 17 17, g32p_row03_traceSegment_030_3948_0017, g32p_row03_traceSegment_030_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 3915 67 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3915 33 34, g32p_row03_traceSegment_030_3915_0033, g32p_row03_traceSegment_030_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3982 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3982 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3982 8 9, g32p_row03_traceSegment_030_3982_0008, g32p_row03_traceSegment_030_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3999 8 9, g32p_row03_traceSegment_030_3999_0008, g32p_row03_traceSegment_030_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 3982 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3982 17 17, g32p_row03_traceSegment_030_3982_0017, g32p_row03_traceSegment_030_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4024 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4016 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4016 8 9, g32p_row03_traceSegment_030_4016_0008, g32p_row03_traceSegment_030_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4033 8 9, g32p_row03_traceSegment_030_4033_0008, g32p_row03_traceSegment_030_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 4016 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4016 17 17, g32p_row03_traceSegment_030_4016_0017, g32p_row03_traceSegment_030_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 3982 68 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3982 34 34, g32p_row03_traceSegment_030_3982_0034, g32p_row03_traceSegment_030_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 3915 135 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3915 67 68, g32p_row03_traceSegment_030_3915_0067, g32p_row03_traceSegment_030_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 3780 270 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3780 135 135, g32p_row03_traceSegment_030_3780_0135, g32p_row03_traceSegment_030_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4066 8 9, g32p_row03_traceSegment_030_4066_0008, g32p_row03_traceSegment_030_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4050 16 17, g32p_row03_traceSegment_030_4050_0016, g32p_row03_traceSegment_030_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4083 8 9, g32p_row03_traceSegment_030_4083_0008, g32p_row03_traceSegment_030_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4100 8 9, g32p_row03_traceSegment_030_4100_0008, g32p_row03_traceSegment_030_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4083 17 17, g32p_row03_traceSegment_030_4083_0017, g32p_row03_traceSegment_030_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4050 33 34, g32p_row03_traceSegment_030_4050_0033, g32p_row03_traceSegment_030_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4117 8 9, g32p_row03_traceSegment_030_4117_0008, g32p_row03_traceSegment_030_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4142 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4134 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4134 8 9, g32p_row03_traceSegment_030_4134_0008, g32p_row03_traceSegment_030_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 4117 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4117 17 17, g32p_row03_traceSegment_030_4117_0017, g32p_row03_traceSegment_030_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4151 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4151 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4151 8 9, g32p_row03_traceSegment_030_4151_0008, g32p_row03_traceSegment_030_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4168 8 9, g32p_row03_traceSegment_030_4168_0008, g32p_row03_traceSegment_030_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 4151 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4151 17 17, g32p_row03_traceSegment_030_4151_0017, g32p_row03_traceSegment_030_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 4117 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4117 34 34, g32p_row03_traceSegment_030_4117_0034, g32p_row03_traceSegment_030_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 4050 135 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4050 67 68, g32p_row03_traceSegment_030_4050_0067, g32p_row03_traceSegment_030_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_030 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4201 8 9, g32p_row03_traceSegment_030_4201_0008, g32p_row03_traceSegment_030_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_030 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4185 16 17, g32p_row03_traceSegment_030_4185_0016, g32p_row03_traceSegment_030_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4226 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4218 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4218 8 9, g32p_row03_traceSegment_030_4218_0008, g32p_row03_traceSegment_030_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4235 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4243 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4235 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4235 8 9, g32p_row03_traceSegment_030_4235_0008, g32p_row03_traceSegment_030_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 4218 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4218 17 17, g32p_row03_traceSegment_030_4218_0017, g32p_row03_traceSegment_030_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_030 4185 67 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4185 33 34, g32p_row03_traceSegment_030_4185_0033, g32p_row03_traceSegment_030_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4252 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4260 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4252 17 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4252 8 9, g32p_row03_traceSegment_030_4252_0008, g32p_row03_traceSegment_030_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4269 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4277 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4269 17 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4269 8 9, g32p_row03_traceSegment_030_4269_0008, g32p_row03_traceSegment_030_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 4252 34 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4252 17 17, g32p_row03_traceSegment_030_4252_0017, g32p_row03_traceSegment_030_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4286 8 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4294 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4286 17 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4286 8 9, g32p_row03_traceSegment_030_4286_0008, g32p_row03_traceSegment_030_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_030 4303 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_030 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_030_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_030 4303 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4303 8 9, g32p_row03_traceSegment_030_4303_0008, g32p_row03_traceSegment_030_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_030 4286 34 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4286 17 17, g32p_row03_traceSegment_030_4286_0017, g32p_row03_traceSegment_030_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_030 4252 68 = [0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4252 34 34, g32p_row03_traceSegment_030_4252_0034, g32p_row03_traceSegment_030_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_030 4185 135 = [0, 22] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4185 67 68, g32p_row03_traceSegment_030_4185_0067, g32p_row03_traceSegment_030_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_030_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_030 4050 270 = [0, 25] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 4050 135 135, g32p_row03_traceSegment_030_4050_0135, g32p_row03_traceSegment_030_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_030 3780 540 = [0, 40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3780 270 270, g32p_row03_traceSegment_030_3780_0270, g32p_row03_traceSegment_030_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_030_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_030 3240 1080 = [0, 76] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 3240 540 540, g32p_row03_traceSegment_030_3240_0540, g32p_row03_traceSegment_030_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_030_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_030 2160 2160 = [0, 111] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 2160 1080 1080, g32p_row03_traceSegment_030_2160_1080, g32p_row03_traceSegment_030_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_030_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_030 0 4320 = [0, 240] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_030 0 2160 2160, g32p_row03_traceSegment_030_0000_2160, g32p_row03_traceSegment_030_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_030 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 30 = [0, 240] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_030_0000_4320

end HodgeLean.Foundations.Program

end
end
