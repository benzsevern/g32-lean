import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_022 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 22 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_022_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 16 8 9, g32p_row03_traceSegment_022_0016_0008, g32p_row03_traceSegment_022_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 0 16 17, g32p_row03_traceSegment_022_0000_0016, g32p_row03_traceSegment_022_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 33 8 9, g32p_row03_traceSegment_022_0033_0008, g32p_row03_traceSegment_022_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 50 8 9, g32p_row03_traceSegment_022_0050_0008, g32p_row03_traceSegment_022_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 33 17 17, g32p_row03_traceSegment_022_0033_0017, g32p_row03_traceSegment_022_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 0 33 34, g32p_row03_traceSegment_022_0000_0033, g32p_row03_traceSegment_022_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 67 8 9, g32p_row03_traceSegment_022_0067_0008, g32p_row03_traceSegment_022_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 84 8 9, g32p_row03_traceSegment_022_0084_0008, g32p_row03_traceSegment_022_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 67 17 17, g32p_row03_traceSegment_022_0067_0017, g32p_row03_traceSegment_022_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 101 8 9, g32p_row03_traceSegment_022_0101_0008, g32p_row03_traceSegment_022_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 126 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 118 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 118 8 9, g32p_row03_traceSegment_022_0118_0008, g32p_row03_traceSegment_022_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 101 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 101 17 17, g32p_row03_traceSegment_022_0101_0017, g32p_row03_traceSegment_022_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 67 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 67 34 34, g32p_row03_traceSegment_022_0067_0034, g32p_row03_traceSegment_022_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 0 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 0 67 68, g32p_row03_traceSegment_022_0000_0067, g32p_row03_traceSegment_022_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 135 16 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 159 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 151 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 151 8 9, g32p_row03_traceSegment_022_0151_0008, g32p_row03_traceSegment_022_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 135 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 135 16 17, g32p_row03_traceSegment_022_0135_0016, g32p_row03_traceSegment_022_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 168 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 176 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 168 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 168 8 9, g32p_row03_traceSegment_022_0168_0008, g32p_row03_traceSegment_022_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 185 8 9, g32p_row03_traceSegment_022_0185_0008, g32p_row03_traceSegment_022_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 168 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 168 17 17, g32p_row03_traceSegment_022_0168_0017, g32p_row03_traceSegment_022_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 135 67 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 135 33 34, g32p_row03_traceSegment_022_0135_0033, g32p_row03_traceSegment_022_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 202 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 202 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 202 8 9, g32p_row03_traceSegment_022_0202_0008, g32p_row03_traceSegment_022_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 219 8 9, g32p_row03_traceSegment_022_0219_0008, g32p_row03_traceSegment_022_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 202 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 202 17 17, g32p_row03_traceSegment_022_0202_0017, g32p_row03_traceSegment_022_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 236 8 9, g32p_row03_traceSegment_022_0236_0008, g32p_row03_traceSegment_022_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 253 8 9, g32p_row03_traceSegment_022_0253_0008, g32p_row03_traceSegment_022_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 236 17 17, g32p_row03_traceSegment_022_0236_0017, g32p_row03_traceSegment_022_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 202 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 202 34 34, g32p_row03_traceSegment_022_0202_0034, g32p_row03_traceSegment_022_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 135 135 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 135 67 68, g32p_row03_traceSegment_022_0135_0067, g32p_row03_traceSegment_022_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 0 270 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 0 135 135, g32p_row03_traceSegment_022_0000_0135, g32p_row03_traceSegment_022_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 286 8 9, g32p_row03_traceSegment_022_0286_0008, g32p_row03_traceSegment_022_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 270 16 17, g32p_row03_traceSegment_022_0270_0016, g32p_row03_traceSegment_022_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 303 8 9, g32p_row03_traceSegment_022_0303_0008, g32p_row03_traceSegment_022_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 320 8 9, g32p_row03_traceSegment_022_0320_0008, g32p_row03_traceSegment_022_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 303 17 17, g32p_row03_traceSegment_022_0303_0017, g32p_row03_traceSegment_022_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 270 33 34, g32p_row03_traceSegment_022_0270_0033, g32p_row03_traceSegment_022_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 337 8 9, g32p_row03_traceSegment_022_0337_0008, g32p_row03_traceSegment_022_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 354 8 9, g32p_row03_traceSegment_022_0354_0008, g32p_row03_traceSegment_022_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 337 17 17, g32p_row03_traceSegment_022_0337_0017, g32p_row03_traceSegment_022_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 371 8 9, g32p_row03_traceSegment_022_0371_0008, g32p_row03_traceSegment_022_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 388 8 9, g32p_row03_traceSegment_022_0388_0008, g32p_row03_traceSegment_022_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 371 17 17, g32p_row03_traceSegment_022_0371_0017, g32p_row03_traceSegment_022_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 337 34 34, g32p_row03_traceSegment_022_0337_0034, g32p_row03_traceSegment_022_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 270 67 68, g32p_row03_traceSegment_022_0270_0067, g32p_row03_traceSegment_022_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 421 8 9, g32p_row03_traceSegment_022_0421_0008, g32p_row03_traceSegment_022_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 405 16 17, g32p_row03_traceSegment_022_0405_0016, g32p_row03_traceSegment_022_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 438 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 438 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 438 8 9, g32p_row03_traceSegment_022_0438_0008, g32p_row03_traceSegment_022_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 455 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 463 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 455 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 455 8 9, g32p_row03_traceSegment_022_0455_0008, g32p_row03_traceSegment_022_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 438 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 438 17 17, g32p_row03_traceSegment_022_0438_0017, g32p_row03_traceSegment_022_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 405 67 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 405 33 34, g32p_row03_traceSegment_022_0405_0033, g32p_row03_traceSegment_022_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 472 8 9, g32p_row03_traceSegment_022_0472_0008, g32p_row03_traceSegment_022_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 497 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 489 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 489 8 9, g32p_row03_traceSegment_022_0489_0008, g32p_row03_traceSegment_022_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 472 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 472 17 17, g32p_row03_traceSegment_022_0472_0017, g32p_row03_traceSegment_022_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 506 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 514 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 506 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 506 8 9, g32p_row03_traceSegment_022_0506_0008, g32p_row03_traceSegment_022_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 523 8 9, g32p_row03_traceSegment_022_0523_0008, g32p_row03_traceSegment_022_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 506 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 506 17 17, g32p_row03_traceSegment_022_0506_0017, g32p_row03_traceSegment_022_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 472 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 472 34 34, g32p_row03_traceSegment_022_0472_0034, g32p_row03_traceSegment_022_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 405 135 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 405 67 68, g32p_row03_traceSegment_022_0405_0067, g32p_row03_traceSegment_022_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 270 270 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 270 135 135, g32p_row03_traceSegment_022_0270_0135, g32p_row03_traceSegment_022_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_022 0 540 = [13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 0 270 270, g32p_row03_traceSegment_022_0000_0270, g32p_row03_traceSegment_022_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 556 8 9, g32p_row03_traceSegment_022_0556_0008, g32p_row03_traceSegment_022_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 540 16 17, g32p_row03_traceSegment_022_0540_0016, g32p_row03_traceSegment_022_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 581 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 573 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 573 8 9, g32p_row03_traceSegment_022_0573_0008, g32p_row03_traceSegment_022_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 590 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 590 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 590 8 9, g32p_row03_traceSegment_022_0590_0008, g32p_row03_traceSegment_022_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 573 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 573 17 17, g32p_row03_traceSegment_022_0573_0017, g32p_row03_traceSegment_022_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 540 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 540 33 34, g32p_row03_traceSegment_022_0540_0033, g32p_row03_traceSegment_022_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 615 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 607 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 607 8 9, g32p_row03_traceSegment_022_0607_0008, g32p_row03_traceSegment_022_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 624 8 9, g32p_row03_traceSegment_022_0624_0008, g32p_row03_traceSegment_022_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 607 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 607 17 17, g32p_row03_traceSegment_022_0607_0017, g32p_row03_traceSegment_022_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 641 8 9, g32p_row03_traceSegment_022_0641_0008, g32p_row03_traceSegment_022_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 658 8 9, g32p_row03_traceSegment_022_0658_0008, g32p_row03_traceSegment_022_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 641 17 17, g32p_row03_traceSegment_022_0641_0017, g32p_row03_traceSegment_022_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 607 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 607 34 34, g32p_row03_traceSegment_022_0607_0034, g32p_row03_traceSegment_022_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 540 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 540 67 68, g32p_row03_traceSegment_022_0540_0067, g32p_row03_traceSegment_022_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 691 8 9, g32p_row03_traceSegment_022_0691_0008, g32p_row03_traceSegment_022_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 675 16 17, g32p_row03_traceSegment_022_0675_0016, g32p_row03_traceSegment_022_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 708 8 9, g32p_row03_traceSegment_022_0708_0008, g32p_row03_traceSegment_022_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 725 8 9, g32p_row03_traceSegment_022_0725_0008, g32p_row03_traceSegment_022_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 708 17 17, g32p_row03_traceSegment_022_0708_0017, g32p_row03_traceSegment_022_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 675 33 34, g32p_row03_traceSegment_022_0675_0033, g32p_row03_traceSegment_022_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 742 8 9, g32p_row03_traceSegment_022_0742_0008, g32p_row03_traceSegment_022_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 759 8 9, g32p_row03_traceSegment_022_0759_0008, g32p_row03_traceSegment_022_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 742 17 17, g32p_row03_traceSegment_022_0742_0017, g32p_row03_traceSegment_022_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 776 8 9, g32p_row03_traceSegment_022_0776_0008, g32p_row03_traceSegment_022_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 793 8 9, g32p_row03_traceSegment_022_0793_0008, g32p_row03_traceSegment_022_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 776 17 17, g32p_row03_traceSegment_022_0776_0017, g32p_row03_traceSegment_022_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 742 34 34, g32p_row03_traceSegment_022_0742_0034, g32p_row03_traceSegment_022_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 675 67 68, g32p_row03_traceSegment_022_0675_0067, g32p_row03_traceSegment_022_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 540 270 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 540 135 135, g32p_row03_traceSegment_022_0540_0135, g32p_row03_traceSegment_022_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 834 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 826 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 826 8 9, g32p_row03_traceSegment_022_0826_0008, g32p_row03_traceSegment_022_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 810 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 810 16 17, g32p_row03_traceSegment_022_0810_0016, g32p_row03_traceSegment_022_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 843 8 9, g32p_row03_traceSegment_022_0843_0008, g32p_row03_traceSegment_022_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 860 8 9, g32p_row03_traceSegment_022_0860_0008, g32p_row03_traceSegment_022_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 843 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 843 17 17, g32p_row03_traceSegment_022_0843_0017, g32p_row03_traceSegment_022_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 810 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 810 33 34, g32p_row03_traceSegment_022_0810_0033, g32p_row03_traceSegment_022_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 877 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 877 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 877 8 9, g32p_row03_traceSegment_022_0877_0008, g32p_row03_traceSegment_022_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 894 8 9, g32p_row03_traceSegment_022_0894_0008, g32p_row03_traceSegment_022_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 877 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 877 17 17, g32p_row03_traceSegment_022_0877_0017, g32p_row03_traceSegment_022_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 911 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 911 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 911 8 9, g32p_row03_traceSegment_022_0911_0008, g32p_row03_traceSegment_022_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 928 8 9, g32p_row03_traceSegment_022_0928_0008, g32p_row03_traceSegment_022_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 911 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 911 17 17, g32p_row03_traceSegment_022_0911_0017, g32p_row03_traceSegment_022_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 877 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 877 34 34, g32p_row03_traceSegment_022_0877_0034, g32p_row03_traceSegment_022_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 810 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 810 67 68, g32p_row03_traceSegment_022_0810_0067, g32p_row03_traceSegment_022_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 969 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 961 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 961 8 9, g32p_row03_traceSegment_022_0961_0008, g32p_row03_traceSegment_022_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 945 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 945 16 17, g32p_row03_traceSegment_022_0945_0016, g32p_row03_traceSegment_022_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 978 8 9, g32p_row03_traceSegment_022_0978_0008, g32p_row03_traceSegment_022_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 995 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 995 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 995 8 9, g32p_row03_traceSegment_022_0995_0008, g32p_row03_traceSegment_022_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 978 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 978 17 17, g32p_row03_traceSegment_022_0978_0017, g32p_row03_traceSegment_022_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 945 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 945 33 34, g32p_row03_traceSegment_022_0945_0033, g32p_row03_traceSegment_022_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1012 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1012 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1012 8 9, g32p_row03_traceSegment_022_1012_0008, g32p_row03_traceSegment_022_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1029 8 9, g32p_row03_traceSegment_022_1029_0008, g32p_row03_traceSegment_022_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1012 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1012 17 17, g32p_row03_traceSegment_022_1012_0017, g32p_row03_traceSegment_022_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1046 8 9, g32p_row03_traceSegment_022_1046_0008, g32p_row03_traceSegment_022_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1063 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1063 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1063 8 9, g32p_row03_traceSegment_022_1063_0008, g32p_row03_traceSegment_022_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1046 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1046 17 17, g32p_row03_traceSegment_022_1046_0017, g32p_row03_traceSegment_022_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 1012 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1012 34 34, g32p_row03_traceSegment_022_1012_0034, g32p_row03_traceSegment_022_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 945 135 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 945 67 68, g32p_row03_traceSegment_022_0945_0067, g32p_row03_traceSegment_022_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 810 270 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 810 135 135, g32p_row03_traceSegment_022_0810_0135, g32p_row03_traceSegment_022_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_022 540 540 = [10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 540 270 270, g32p_row03_traceSegment_022_0540_0270, g32p_row03_traceSegment_022_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_022 0 1080 = [23] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 0 540 540, g32p_row03_traceSegment_022_0000_0540, g32p_row03_traceSegment_022_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 1080 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1096 8 9, g32p_row03_traceSegment_022_1096_0008, g32p_row03_traceSegment_022_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 1080 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1080 16 17, g32p_row03_traceSegment_022_1080_0016, g32p_row03_traceSegment_022_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1113 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1113 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1113 8 9, g32p_row03_traceSegment_022_1113_0008, g32p_row03_traceSegment_022_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1130 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1130 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1130 8 9, g32p_row03_traceSegment_022_1130_0008, g32p_row03_traceSegment_022_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1113 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1113 17 17, g32p_row03_traceSegment_022_1113_0017, g32p_row03_traceSegment_022_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 1080 67 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1080 33 34, g32p_row03_traceSegment_022_1080_0033, g32p_row03_traceSegment_022_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1147 8 9, g32p_row03_traceSegment_022_1147_0008, g32p_row03_traceSegment_022_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1172 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1164 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1164 8 9, g32p_row03_traceSegment_022_1164_0008, g32p_row03_traceSegment_022_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1147 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1147 17 17, g32p_row03_traceSegment_022_1147_0017, g32p_row03_traceSegment_022_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1189 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1181 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1181 8 9, g32p_row03_traceSegment_022_1181_0008, g32p_row03_traceSegment_022_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1198 8 9, g32p_row03_traceSegment_022_1198_0008, g32p_row03_traceSegment_022_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1181 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1181 17 17, g32p_row03_traceSegment_022_1181_0017, g32p_row03_traceSegment_022_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 1147 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1147 34 34, g32p_row03_traceSegment_022_1147_0034, g32p_row03_traceSegment_022_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 1080 135 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1080 67 68, g32p_row03_traceSegment_022_1080_0067, g32p_row03_traceSegment_022_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 1215 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1231 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1239 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1231 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1231 8 9, g32p_row03_traceSegment_022_1231_0008, g32p_row03_traceSegment_022_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 1215 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1215 16 17, g32p_row03_traceSegment_022_1215_0016, g32p_row03_traceSegment_022_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1248 8 9, g32p_row03_traceSegment_022_1248_0008, g32p_row03_traceSegment_022_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1265 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1273 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1265 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1265 8 9, g32p_row03_traceSegment_022_1265_0008, g32p_row03_traceSegment_022_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1248 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1248 17 17, g32p_row03_traceSegment_022_1248_0017, g32p_row03_traceSegment_022_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 1215 67 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1215 33 34, g32p_row03_traceSegment_022_1215_0033, g32p_row03_traceSegment_022_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1290 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1282 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1282 8 9, g32p_row03_traceSegment_022_1282_0008, g32p_row03_traceSegment_022_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1307 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1299 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1299 8 9, g32p_row03_traceSegment_022_1299_0008, g32p_row03_traceSegment_022_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1282 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1282 17 17, g32p_row03_traceSegment_022_1282_0017, g32p_row03_traceSegment_022_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1316 8 9, g32p_row03_traceSegment_022_1316_0008, g32p_row03_traceSegment_022_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1341 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1333 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1333 8 9, g32p_row03_traceSegment_022_1333_0008, g32p_row03_traceSegment_022_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1316 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1316 17 17, g32p_row03_traceSegment_022_1316_0017, g32p_row03_traceSegment_022_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 1282 68 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1282 34 34, g32p_row03_traceSegment_022_1282_0034, g32p_row03_traceSegment_022_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 1215 135 = [9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1215 67 68, g32p_row03_traceSegment_022_1215_0067, g32p_row03_traceSegment_022_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 1080 270 = [14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1080 135 135, g32p_row03_traceSegment_022_1080_0135, g32p_row03_traceSegment_022_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1374 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1366 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1366 8 9, g32p_row03_traceSegment_022_1366_0008, g32p_row03_traceSegment_022_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 1350 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1350 16 17, g32p_row03_traceSegment_022_1350_0016, g32p_row03_traceSegment_022_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1383 8 9, g32p_row03_traceSegment_022_1383_0008, g32p_row03_traceSegment_022_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1400 8 9, g32p_row03_traceSegment_022_1400_0008, g32p_row03_traceSegment_022_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1383 17 17, g32p_row03_traceSegment_022_1383_0017, g32p_row03_traceSegment_022_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 1350 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1350 33 34, g32p_row03_traceSegment_022_1350_0033, g32p_row03_traceSegment_022_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1417 8 9, g32p_row03_traceSegment_022_1417_0008, g32p_row03_traceSegment_022_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1434 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1434 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1434 8 9, g32p_row03_traceSegment_022_1434_0008, g32p_row03_traceSegment_022_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1417 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1417 17 17, g32p_row03_traceSegment_022_1417_0017, g32p_row03_traceSegment_022_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1451 8 9, g32p_row03_traceSegment_022_1451_0008, g32p_row03_traceSegment_022_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1468 8 9, g32p_row03_traceSegment_022_1468_0008, g32p_row03_traceSegment_022_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1451 17 17, g32p_row03_traceSegment_022_1451_0017, g32p_row03_traceSegment_022_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 1417 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1417 34 34, g32p_row03_traceSegment_022_1417_0034, g32p_row03_traceSegment_022_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 1350 135 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1350 67 68, g32p_row03_traceSegment_022_1350_0067, g32p_row03_traceSegment_022_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 1485 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1501 8 9, g32p_row03_traceSegment_022_1501_0008, g32p_row03_traceSegment_022_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 1485 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1485 16 17, g32p_row03_traceSegment_022_1485_0016, g32p_row03_traceSegment_022_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1518 8 9, g32p_row03_traceSegment_022_1518_0008, g32p_row03_traceSegment_022_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1535 8 9, g32p_row03_traceSegment_022_1535_0008, g32p_row03_traceSegment_022_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1518 17 17, g32p_row03_traceSegment_022_1518_0017, g32p_row03_traceSegment_022_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 1485 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1485 33 34, g32p_row03_traceSegment_022_1485_0033, g32p_row03_traceSegment_022_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1552 8 9, g32p_row03_traceSegment_022_1552_0008, g32p_row03_traceSegment_022_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1569 8 9, g32p_row03_traceSegment_022_1569_0008, g32p_row03_traceSegment_022_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1552 17 17, g32p_row03_traceSegment_022_1552_0017, g32p_row03_traceSegment_022_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1586 8 9, g32p_row03_traceSegment_022_1586_0008, g32p_row03_traceSegment_022_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1603 8 9, g32p_row03_traceSegment_022_1603_0008, g32p_row03_traceSegment_022_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1586 17 17, g32p_row03_traceSegment_022_1586_0017, g32p_row03_traceSegment_022_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1552 34 34, g32p_row03_traceSegment_022_1552_0034, g32p_row03_traceSegment_022_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 1485 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1485 67 68, g32p_row03_traceSegment_022_1485_0067, g32p_row03_traceSegment_022_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 1350 270 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1350 135 135, g32p_row03_traceSegment_022_1350_0135, g32p_row03_traceSegment_022_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_022 1080 540 = [17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1080 270 270, g32p_row03_traceSegment_022_1080_0270, g32p_row03_traceSegment_022_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1636 8 9, g32p_row03_traceSegment_022_1636_0008, g32p_row03_traceSegment_022_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1620 16 17, g32p_row03_traceSegment_022_1620_0016, g32p_row03_traceSegment_022_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1653 8 9, g32p_row03_traceSegment_022_1653_0008, g32p_row03_traceSegment_022_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1670 8 9, g32p_row03_traceSegment_022_1670_0008, g32p_row03_traceSegment_022_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1653 17 17, g32p_row03_traceSegment_022_1653_0017, g32p_row03_traceSegment_022_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1620 33 34, g32p_row03_traceSegment_022_1620_0033, g32p_row03_traceSegment_022_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1687 8 9, g32p_row03_traceSegment_022_1687_0008, g32p_row03_traceSegment_022_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1704 8 9, g32p_row03_traceSegment_022_1704_0008, g32p_row03_traceSegment_022_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1687 17 17, g32p_row03_traceSegment_022_1687_0017, g32p_row03_traceSegment_022_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1721 8 9, g32p_row03_traceSegment_022_1721_0008, g32p_row03_traceSegment_022_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1738 8 9, g32p_row03_traceSegment_022_1738_0008, g32p_row03_traceSegment_022_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1721 17 17, g32p_row03_traceSegment_022_1721_0017, g32p_row03_traceSegment_022_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1687 34 34, g32p_row03_traceSegment_022_1687_0034, g32p_row03_traceSegment_022_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 1620 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1620 67 68, g32p_row03_traceSegment_022_1620_0067, g32p_row03_traceSegment_022_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1771 8 9, g32p_row03_traceSegment_022_1771_0008, g32p_row03_traceSegment_022_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1755 16 17, g32p_row03_traceSegment_022_1755_0016, g32p_row03_traceSegment_022_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1788 8 9, g32p_row03_traceSegment_022_1788_0008, g32p_row03_traceSegment_022_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1805 8 9, g32p_row03_traceSegment_022_1805_0008, g32p_row03_traceSegment_022_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1788 17 17, g32p_row03_traceSegment_022_1788_0017, g32p_row03_traceSegment_022_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1755 33 34, g32p_row03_traceSegment_022_1755_0033, g32p_row03_traceSegment_022_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1822 8 9, g32p_row03_traceSegment_022_1822_0008, g32p_row03_traceSegment_022_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1839 8 9, g32p_row03_traceSegment_022_1839_0008, g32p_row03_traceSegment_022_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1822 17 17, g32p_row03_traceSegment_022_1822_0017, g32p_row03_traceSegment_022_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1856 8 9, g32p_row03_traceSegment_022_1856_0008, g32p_row03_traceSegment_022_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1873 8 9, g32p_row03_traceSegment_022_1873_0008, g32p_row03_traceSegment_022_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1856 17 17, g32p_row03_traceSegment_022_1856_0017, g32p_row03_traceSegment_022_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1822 34 34, g32p_row03_traceSegment_022_1822_0034, g32p_row03_traceSegment_022_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 1755 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1755 67 68, g32p_row03_traceSegment_022_1755_0067, g32p_row03_traceSegment_022_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 1620 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1620 135 135, g32p_row03_traceSegment_022_1620_0135, g32p_row03_traceSegment_022_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1906 8 9, g32p_row03_traceSegment_022_1906_0008, g32p_row03_traceSegment_022_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1890 16 17, g32p_row03_traceSegment_022_1890_0016, g32p_row03_traceSegment_022_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1923 8 9, g32p_row03_traceSegment_022_1923_0008, g32p_row03_traceSegment_022_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1940 8 9, g32p_row03_traceSegment_022_1940_0008, g32p_row03_traceSegment_022_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1923 17 17, g32p_row03_traceSegment_022_1923_0017, g32p_row03_traceSegment_022_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1890 33 34, g32p_row03_traceSegment_022_1890_0033, g32p_row03_traceSegment_022_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1957 8 9, g32p_row03_traceSegment_022_1957_0008, g32p_row03_traceSegment_022_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1974 8 9, g32p_row03_traceSegment_022_1974_0008, g32p_row03_traceSegment_022_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1957 17 17, g32p_row03_traceSegment_022_1957_0017, g32p_row03_traceSegment_022_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1991 8 9, g32p_row03_traceSegment_022_1991_0008, g32p_row03_traceSegment_022_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2008 8 9, g32p_row03_traceSegment_022_2008_0008, g32p_row03_traceSegment_022_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1991 17 17, g32p_row03_traceSegment_022_1991_0017, g32p_row03_traceSegment_022_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1957 34 34, g32p_row03_traceSegment_022_1957_0034, g32p_row03_traceSegment_022_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1890 67 68, g32p_row03_traceSegment_022_1890_0067, g32p_row03_traceSegment_022_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2041 8 9, g32p_row03_traceSegment_022_2041_0008, g32p_row03_traceSegment_022_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2025 16 17, g32p_row03_traceSegment_022_2025_0016, g32p_row03_traceSegment_022_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2058 8 9, g32p_row03_traceSegment_022_2058_0008, g32p_row03_traceSegment_022_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2075 8 9, g32p_row03_traceSegment_022_2075_0008, g32p_row03_traceSegment_022_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2058 17 17, g32p_row03_traceSegment_022_2058_0017, g32p_row03_traceSegment_022_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2025 33 34, g32p_row03_traceSegment_022_2025_0033, g32p_row03_traceSegment_022_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2092 8 9, g32p_row03_traceSegment_022_2092_0008, g32p_row03_traceSegment_022_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2109 8 9, g32p_row03_traceSegment_022_2109_0008, g32p_row03_traceSegment_022_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2092 17 17, g32p_row03_traceSegment_022_2092_0017, g32p_row03_traceSegment_022_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2126 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2126 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2126 8 9, g32p_row03_traceSegment_022_2126_0008, g32p_row03_traceSegment_022_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2151 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2143 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2143 8 9, g32p_row03_traceSegment_022_2143_0008, g32p_row03_traceSegment_022_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2126 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2126 17 17, g32p_row03_traceSegment_022_2126_0017, g32p_row03_traceSegment_022_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 2092 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2092 34 34, g32p_row03_traceSegment_022_2092_0034, g32p_row03_traceSegment_022_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 2025 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2025 67 68, g32p_row03_traceSegment_022_2025_0067, g32p_row03_traceSegment_022_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 1890 270 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1890 135 135, g32p_row03_traceSegment_022_1890_0135, g32p_row03_traceSegment_022_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_022 1620 540 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1620 270 270, g32p_row03_traceSegment_022_1620_0270, g32p_row03_traceSegment_022_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_022_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_022 1080 1080 = [20] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 1080 540 540, g32p_row03_traceSegment_022_1080_0540, g32p_row03_traceSegment_022_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_022 0 2160 = [43] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 0 1080 1080, g32p_row03_traceSegment_022_0000_1080, g32p_row03_traceSegment_022_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 2160 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2176 8 9, g32p_row03_traceSegment_022_2176_0008, g32p_row03_traceSegment_022_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 2160 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2160 16 17, g32p_row03_traceSegment_022_2160_0016, g32p_row03_traceSegment_022_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2201 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2193 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2193 8 9, g32p_row03_traceSegment_022_2193_0008, g32p_row03_traceSegment_022_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2210 8 9, g32p_row03_traceSegment_022_2210_0008, g32p_row03_traceSegment_022_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2193 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2193 17 17, g32p_row03_traceSegment_022_2193_0017, g32p_row03_traceSegment_022_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 2160 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2160 33 34, g32p_row03_traceSegment_022_2160_0033, g32p_row03_traceSegment_022_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2227 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2235 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2227 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2227 8 9, g32p_row03_traceSegment_022_2227_0008, g32p_row03_traceSegment_022_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2244 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2244 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2244 8 9, g32p_row03_traceSegment_022_2244_0008, g32p_row03_traceSegment_022_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2227 34 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2227 17 17, g32p_row03_traceSegment_022_2227_0017, g32p_row03_traceSegment_022_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2269 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2261 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2261 8 9, g32p_row03_traceSegment_022_2261_0008, g32p_row03_traceSegment_022_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2278 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2278 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2278 8 9, g32p_row03_traceSegment_022_2278_0008, g32p_row03_traceSegment_022_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2261 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2261 17 17, g32p_row03_traceSegment_022_2261_0017, g32p_row03_traceSegment_022_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 2227 68 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2227 34 34, g32p_row03_traceSegment_022_2227_0034, g32p_row03_traceSegment_022_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 2160 135 = [9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2160 67 68, g32p_row03_traceSegment_022_2160_0067, g32p_row03_traceSegment_022_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 2295 16 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2311 8 9, g32p_row03_traceSegment_022_2311_0008, g32p_row03_traceSegment_022_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 2295 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2295 16 17, g32p_row03_traceSegment_022_2295_0016, g32p_row03_traceSegment_022_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2328 8 9, g32p_row03_traceSegment_022_2328_0008, g32p_row03_traceSegment_022_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2345 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2345 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2345 8 9, g32p_row03_traceSegment_022_2345_0008, g32p_row03_traceSegment_022_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2328 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2328 17 17, g32p_row03_traceSegment_022_2328_0017, g32p_row03_traceSegment_022_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 2295 67 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2295 33 34, g32p_row03_traceSegment_022_2295_0033, g32p_row03_traceSegment_022_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2362 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2370 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2362 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2362 8 9, g32p_row03_traceSegment_022_2362_0008, g32p_row03_traceSegment_022_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2379 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2387 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2379 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2379 8 9, g32p_row03_traceSegment_022_2379_0008, g32p_row03_traceSegment_022_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2362 34 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2362 17 17, g32p_row03_traceSegment_022_2362_0017, g32p_row03_traceSegment_022_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2404 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2396 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2396 8 9, g32p_row03_traceSegment_022_2396_0008, g32p_row03_traceSegment_022_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2413 8 = [3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2413 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2413 8 9, g32p_row03_traceSegment_022_2413_0008, g32p_row03_traceSegment_022_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2396 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2396 17 17, g32p_row03_traceSegment_022_2396_0017, g32p_row03_traceSegment_022_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 2362 68 = [9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2362 34 34, g32p_row03_traceSegment_022_2362_0034, g32p_row03_traceSegment_022_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 2295 135 = [12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2295 67 68, g32p_row03_traceSegment_022_2295_0067, g32p_row03_traceSegment_022_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 2160 270 = [21] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2160 135 135, g32p_row03_traceSegment_022_2160_0135, g32p_row03_traceSegment_022_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 2430 16 = [3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2446 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2446 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2446 8 9, g32p_row03_traceSegment_022_2446_0008, g32p_row03_traceSegment_022_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 2430 33 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2430 16 17, g32p_row03_traceSegment_022_2430_0016, g32p_row03_traceSegment_022_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2471 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2463 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2463 8 9, g32p_row03_traceSegment_022_2463_0008, g32p_row03_traceSegment_022_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2488 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2480 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2480 8 9, g32p_row03_traceSegment_022_2480_0008, g32p_row03_traceSegment_022_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2463 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2463 17 17, g32p_row03_traceSegment_022_2463_0017, g32p_row03_traceSegment_022_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 2430 67 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2430 33 34, g32p_row03_traceSegment_022_2430_0033, g32p_row03_traceSegment_022_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2497 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2505 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2497 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2497 8 9, g32p_row03_traceSegment_022_2497_0008, g32p_row03_traceSegment_022_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2522 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2514 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2514 8 9, g32p_row03_traceSegment_022_2514_0008, g32p_row03_traceSegment_022_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2497 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2497 17 17, g32p_row03_traceSegment_022_2497_0017, g32p_row03_traceSegment_022_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2539 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2531 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2531 8 9, g32p_row03_traceSegment_022_2531_0008, g32p_row03_traceSegment_022_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2548 8 9, g32p_row03_traceSegment_022_2548_0008, g32p_row03_traceSegment_022_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2531 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2531 17 17, g32p_row03_traceSegment_022_2531_0017, g32p_row03_traceSegment_022_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 2497 68 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2497 34 34, g32p_row03_traceSegment_022_2497_0034, g32p_row03_traceSegment_022_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 2430 135 = [12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2430 67 68, g32p_row03_traceSegment_022_2430_0067, g32p_row03_traceSegment_022_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2589 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2581 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2581 8 9, g32p_row03_traceSegment_022_2581_0008, g32p_row03_traceSegment_022_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 2565 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2565 16 17, g32p_row03_traceSegment_022_2565_0016, g32p_row03_traceSegment_022_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2598 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2606 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2598 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2598 8 9, g32p_row03_traceSegment_022_2598_0008, g32p_row03_traceSegment_022_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2615 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2623 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2615 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2615 8 9, g32p_row03_traceSegment_022_2615_0008, g32p_row03_traceSegment_022_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2598 34 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2598 17 17, g32p_row03_traceSegment_022_2598_0017, g32p_row03_traceSegment_022_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 2565 67 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2565 33 34, g32p_row03_traceSegment_022_2565_0033, g32p_row03_traceSegment_022_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2632 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2632 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2632 8 9, g32p_row03_traceSegment_022_2632_0008, g32p_row03_traceSegment_022_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2649 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2649 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2649 8 9, g32p_row03_traceSegment_022_2649_0008, g32p_row03_traceSegment_022_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2632 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2632 17 17, g32p_row03_traceSegment_022_2632_0017, g32p_row03_traceSegment_022_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2674 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2666 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2666 8 9, g32p_row03_traceSegment_022_2666_0008, g32p_row03_traceSegment_022_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2683 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2691 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2683 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2683 8 9, g32p_row03_traceSegment_022_2683_0008, g32p_row03_traceSegment_022_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2666 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2666 17 17, g32p_row03_traceSegment_022_2666_0017, g32p_row03_traceSegment_022_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 2632 68 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2632 34 34, g32p_row03_traceSegment_022_2632_0034, g32p_row03_traceSegment_022_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 2565 135 = [12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2565 67 68, g32p_row03_traceSegment_022_2565_0067, g32p_row03_traceSegment_022_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 2430 270 = [24] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2430 135 135, g32p_row03_traceSegment_022_2430_0135, g32p_row03_traceSegment_022_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_022 2160 540 = [45] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2160 270 270, g32p_row03_traceSegment_022_2160_0270, g32p_row03_traceSegment_022_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 2700 16 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2724 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2716 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2716 8 9, g32p_row03_traceSegment_022_2716_0008, g32p_row03_traceSegment_022_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 2700 33 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2700 16 17, g32p_row03_traceSegment_022_2700_0016, g32p_row03_traceSegment_022_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2741 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2733 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2733 8 9, g32p_row03_traceSegment_022_2733_0008, g32p_row03_traceSegment_022_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2750 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2750 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2750 8 9, g32p_row03_traceSegment_022_2750_0008, g32p_row03_traceSegment_022_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2733 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2733 17 17, g32p_row03_traceSegment_022_2733_0017, g32p_row03_traceSegment_022_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 2700 67 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2700 33 34, g32p_row03_traceSegment_022_2700_0033, g32p_row03_traceSegment_022_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2767 8 9, g32p_row03_traceSegment_022_2767_0008, g32p_row03_traceSegment_022_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2792 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2784 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2784 8 9, g32p_row03_traceSegment_022_2784_0008, g32p_row03_traceSegment_022_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2767 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2767 17 17, g32p_row03_traceSegment_022_2767_0017, g32p_row03_traceSegment_022_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2801 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2809 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2801 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2801 8 9, g32p_row03_traceSegment_022_2801_0008, g32p_row03_traceSegment_022_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2826 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2818 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2818 8 9, g32p_row03_traceSegment_022_2818_0008, g32p_row03_traceSegment_022_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2801 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2801 17 17, g32p_row03_traceSegment_022_2801_0017, g32p_row03_traceSegment_022_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 2767 68 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2767 34 34, g32p_row03_traceSegment_022_2767_0034, g32p_row03_traceSegment_022_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 2700 135 = [10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2700 67 68, g32p_row03_traceSegment_022_2700_0067, g32p_row03_traceSegment_022_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 2835 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2851 8 9, g32p_row03_traceSegment_022_2851_0008, g32p_row03_traceSegment_022_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 2835 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2835 16 17, g32p_row03_traceSegment_022_2835_0016, g32p_row03_traceSegment_022_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2868 8 9, g32p_row03_traceSegment_022_2868_0008, g32p_row03_traceSegment_022_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2885 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2885 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2885 8 9, g32p_row03_traceSegment_022_2885_0008, g32p_row03_traceSegment_022_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2868 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2868 17 17, g32p_row03_traceSegment_022_2868_0017, g32p_row03_traceSegment_022_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 2835 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2835 33 34, g32p_row03_traceSegment_022_2835_0033, g32p_row03_traceSegment_022_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2902 8 9, g32p_row03_traceSegment_022_2902_0008, g32p_row03_traceSegment_022_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2919 8 9, g32p_row03_traceSegment_022_2919_0008, g32p_row03_traceSegment_022_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2902 17 17, g32p_row03_traceSegment_022_2902_0017, g32p_row03_traceSegment_022_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2936 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2944 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2936 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2936 8 9, g32p_row03_traceSegment_022_2936_0008, g32p_row03_traceSegment_022_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2961 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2953 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2953 8 9, g32p_row03_traceSegment_022_2953_0008, g32p_row03_traceSegment_022_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 2936 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2936 17 17, g32p_row03_traceSegment_022_2936_0017, g32p_row03_traceSegment_022_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 2902 68 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2902 34 34, g32p_row03_traceSegment_022_2902_0034, g32p_row03_traceSegment_022_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 2835 135 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2835 67 68, g32p_row03_traceSegment_022_2835_0067, g32p_row03_traceSegment_022_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 2700 270 = [16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2700 135 135, g32p_row03_traceSegment_022_2700_0135, g32p_row03_traceSegment_022_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 2986 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 2986 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2986 8 9, g32p_row03_traceSegment_022_2986_0008, g32p_row03_traceSegment_022_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 2970 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2970 16 17, g32p_row03_traceSegment_022_2970_0016, g32p_row03_traceSegment_022_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3003 8 9, g32p_row03_traceSegment_022_3003_0008, g32p_row03_traceSegment_022_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3020 8 9, g32p_row03_traceSegment_022_3020_0008, g32p_row03_traceSegment_022_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3003 17 17, g32p_row03_traceSegment_022_3003_0017, g32p_row03_traceSegment_022_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 2970 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2970 33 34, g32p_row03_traceSegment_022_2970_0033, g32p_row03_traceSegment_022_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3037 8 9, g32p_row03_traceSegment_022_3037_0008, g32p_row03_traceSegment_022_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3054 8 9, g32p_row03_traceSegment_022_3054_0008, g32p_row03_traceSegment_022_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3037 17 17, g32p_row03_traceSegment_022_3037_0017, g32p_row03_traceSegment_022_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3071 8 9, g32p_row03_traceSegment_022_3071_0008, g32p_row03_traceSegment_022_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3088 8 9, g32p_row03_traceSegment_022_3088_0008, g32p_row03_traceSegment_022_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3071 17 17, g32p_row03_traceSegment_022_3071_0017, g32p_row03_traceSegment_022_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3037 34 34, g32p_row03_traceSegment_022_3037_0034, g32p_row03_traceSegment_022_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 2970 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2970 67 68, g32p_row03_traceSegment_022_2970_0067, g32p_row03_traceSegment_022_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3121 8 9, g32p_row03_traceSegment_022_3121_0008, g32p_row03_traceSegment_022_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3105 16 17, g32p_row03_traceSegment_022_3105_0016, g32p_row03_traceSegment_022_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3138 8 9, g32p_row03_traceSegment_022_3138_0008, g32p_row03_traceSegment_022_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3155 8 9, g32p_row03_traceSegment_022_3155_0008, g32p_row03_traceSegment_022_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3138 17 17, g32p_row03_traceSegment_022_3138_0017, g32p_row03_traceSegment_022_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3105 33 34, g32p_row03_traceSegment_022_3105_0033, g32p_row03_traceSegment_022_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3172 8 9, g32p_row03_traceSegment_022_3172_0008, g32p_row03_traceSegment_022_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3189 8 9, g32p_row03_traceSegment_022_3189_0008, g32p_row03_traceSegment_022_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3172 17 17, g32p_row03_traceSegment_022_3172_0017, g32p_row03_traceSegment_022_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3206 8 9, g32p_row03_traceSegment_022_3206_0008, g32p_row03_traceSegment_022_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3223 8 9, g32p_row03_traceSegment_022_3223_0008, g32p_row03_traceSegment_022_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3206 17 17, g32p_row03_traceSegment_022_3206_0017, g32p_row03_traceSegment_022_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3172 34 34, g32p_row03_traceSegment_022_3172_0034, g32p_row03_traceSegment_022_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 3105 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3105 67 68, g32p_row03_traceSegment_022_3105_0067, g32p_row03_traceSegment_022_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 2970 270 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2970 135 135, g32p_row03_traceSegment_022_2970_0135, g32p_row03_traceSegment_022_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_022 2700 540 = [17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2700 270 270, g32p_row03_traceSegment_022_2700_0270, g32p_row03_traceSegment_022_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_022 2160 1080 = [62] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2160 540 540, g32p_row03_traceSegment_022_2160_0540, g32p_row03_traceSegment_022_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3256 8 9, g32p_row03_traceSegment_022_3256_0008, g32p_row03_traceSegment_022_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3240 16 17, g32p_row03_traceSegment_022_3240_0016, g32p_row03_traceSegment_022_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3273 8 9, g32p_row03_traceSegment_022_3273_0008, g32p_row03_traceSegment_022_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3290 8 9, g32p_row03_traceSegment_022_3290_0008, g32p_row03_traceSegment_022_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3273 17 17, g32p_row03_traceSegment_022_3273_0017, g32p_row03_traceSegment_022_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3240 33 34, g32p_row03_traceSegment_022_3240_0033, g32p_row03_traceSegment_022_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3307 8 9, g32p_row03_traceSegment_022_3307_0008, g32p_row03_traceSegment_022_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3324 8 9, g32p_row03_traceSegment_022_3324_0008, g32p_row03_traceSegment_022_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3307 17 17, g32p_row03_traceSegment_022_3307_0017, g32p_row03_traceSegment_022_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3341 8 9, g32p_row03_traceSegment_022_3341_0008, g32p_row03_traceSegment_022_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3366 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3358 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3358 8 9, g32p_row03_traceSegment_022_3358_0008, g32p_row03_traceSegment_022_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3341 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3341 17 17, g32p_row03_traceSegment_022_3341_0017, g32p_row03_traceSegment_022_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 3307 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3307 34 34, g32p_row03_traceSegment_022_3307_0034, g32p_row03_traceSegment_022_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 3240 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3240 67 68, g32p_row03_traceSegment_022_3240_0067, g32p_row03_traceSegment_022_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3399 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3391 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3391 8 9, g32p_row03_traceSegment_022_3391_0008, g32p_row03_traceSegment_022_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 3375 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3375 16 17, g32p_row03_traceSegment_022_3375_0016, g32p_row03_traceSegment_022_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3408 8 9, g32p_row03_traceSegment_022_3408_0008, g32p_row03_traceSegment_022_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3425 8 9, g32p_row03_traceSegment_022_3425_0008, g32p_row03_traceSegment_022_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3408 17 17, g32p_row03_traceSegment_022_3408_0017, g32p_row03_traceSegment_022_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 3375 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3375 33 34, g32p_row03_traceSegment_022_3375_0033, g32p_row03_traceSegment_022_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3442 8 9, g32p_row03_traceSegment_022_3442_0008, g32p_row03_traceSegment_022_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3459 8 9, g32p_row03_traceSegment_022_3459_0008, g32p_row03_traceSegment_022_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3442 17 17, g32p_row03_traceSegment_022_3442_0017, g32p_row03_traceSegment_022_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3476 8 9, g32p_row03_traceSegment_022_3476_0008, g32p_row03_traceSegment_022_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3493 8 9, g32p_row03_traceSegment_022_3493_0008, g32p_row03_traceSegment_022_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3476 17 17, g32p_row03_traceSegment_022_3476_0017, g32p_row03_traceSegment_022_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 3442 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3442 34 34, g32p_row03_traceSegment_022_3442_0034, g32p_row03_traceSegment_022_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 3375 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3375 67 68, g32p_row03_traceSegment_022_3375_0067, g32p_row03_traceSegment_022_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 3240 270 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3240 135 135, g32p_row03_traceSegment_022_3240_0135, g32p_row03_traceSegment_022_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3526 8 9, g32p_row03_traceSegment_022_3526_0008, g32p_row03_traceSegment_022_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3510 16 17, g32p_row03_traceSegment_022_3510_0016, g32p_row03_traceSegment_022_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3543 8 9, g32p_row03_traceSegment_022_3543_0008, g32p_row03_traceSegment_022_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3560 8 9, g32p_row03_traceSegment_022_3560_0008, g32p_row03_traceSegment_022_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3543 17 17, g32p_row03_traceSegment_022_3543_0017, g32p_row03_traceSegment_022_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3510 33 34, g32p_row03_traceSegment_022_3510_0033, g32p_row03_traceSegment_022_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3577 8 9, g32p_row03_traceSegment_022_3577_0008, g32p_row03_traceSegment_022_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3602 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3594 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3594 8 9, g32p_row03_traceSegment_022_3594_0008, g32p_row03_traceSegment_022_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3577 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3577 17 17, g32p_row03_traceSegment_022_3577_0017, g32p_row03_traceSegment_022_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3611 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3611 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3611 8 9, g32p_row03_traceSegment_022_3611_0008, g32p_row03_traceSegment_022_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3628 8 9, g32p_row03_traceSegment_022_3628_0008, g32p_row03_traceSegment_022_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3611 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3611 17 17, g32p_row03_traceSegment_022_3611_0017, g32p_row03_traceSegment_022_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 3577 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3577 34 34, g32p_row03_traceSegment_022_3577_0034, g32p_row03_traceSegment_022_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 3510 135 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3510 67 68, g32p_row03_traceSegment_022_3510_0067, g32p_row03_traceSegment_022_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3661 8 9, g32p_row03_traceSegment_022_3661_0008, g32p_row03_traceSegment_022_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3645 16 17, g32p_row03_traceSegment_022_3645_0016, g32p_row03_traceSegment_022_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3686 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3678 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3678 8 9, g32p_row03_traceSegment_022_3678_0008, g32p_row03_traceSegment_022_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3695 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3695 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3695 8 9, g32p_row03_traceSegment_022_3695_0008, g32p_row03_traceSegment_022_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3678 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3678 17 17, g32p_row03_traceSegment_022_3678_0017, g32p_row03_traceSegment_022_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 3645 67 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3645 33 34, g32p_row03_traceSegment_022_3645_0033, g32p_row03_traceSegment_022_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3712 8 9, g32p_row03_traceSegment_022_3712_0008, g32p_row03_traceSegment_022_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3737 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3729 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3729 8 9, g32p_row03_traceSegment_022_3729_0008, g32p_row03_traceSegment_022_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3712 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3712 17 17, g32p_row03_traceSegment_022_3712_0017, g32p_row03_traceSegment_022_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3746 8 9, g32p_row03_traceSegment_022_3746_0008, g32p_row03_traceSegment_022_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3771 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3763 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3763 8 9, g32p_row03_traceSegment_022_3763_0008, g32p_row03_traceSegment_022_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3746 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3746 17 17, g32p_row03_traceSegment_022_3746_0017, g32p_row03_traceSegment_022_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 3712 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3712 34 34, g32p_row03_traceSegment_022_3712_0034, g32p_row03_traceSegment_022_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 3645 135 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3645 67 68, g32p_row03_traceSegment_022_3645_0067, g32p_row03_traceSegment_022_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 3510 270 = [8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3510 135 135, g32p_row03_traceSegment_022_3510_0135, g32p_row03_traceSegment_022_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_022 3240 540 = [10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3240 270 270, g32p_row03_traceSegment_022_3240_0270, g32p_row03_traceSegment_022_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 3780 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3796 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3796 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3796 8 9, g32p_row03_traceSegment_022_3796_0008, g32p_row03_traceSegment_022_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 3780 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3780 16 17, g32p_row03_traceSegment_022_3780_0016, g32p_row03_traceSegment_022_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3821 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3813 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3813 8 9, g32p_row03_traceSegment_022_3813_0008, g32p_row03_traceSegment_022_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3830 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3838 9 = [4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3830 17 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3830 8 9, g32p_row03_traceSegment_022_3830_0008, g32p_row03_traceSegment_022_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3813 34 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3813 17 17, g32p_row03_traceSegment_022_3813_0017, g32p_row03_traceSegment_022_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 3780 67 = [9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3780 33 34, g32p_row03_traceSegment_022_3780_0033, g32p_row03_traceSegment_022_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3847 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3855 9 = [3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3847 17 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3847 8 9, g32p_row03_traceSegment_022_3847_0008, g32p_row03_traceSegment_022_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3864 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3872 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3864 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3864 8 9, g32p_row03_traceSegment_022_3864_0008, g32p_row03_traceSegment_022_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3847 34 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3847 17 17, g32p_row03_traceSegment_022_3847_0017, g32p_row03_traceSegment_022_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3881 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3889 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3881 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3881 8 9, g32p_row03_traceSegment_022_3881_0008, g32p_row03_traceSegment_022_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3898 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3906 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3898 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3898 8 9, g32p_row03_traceSegment_022_3898_0008, g32p_row03_traceSegment_022_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3881 34 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3881 17 17, g32p_row03_traceSegment_022_3881_0017, g32p_row03_traceSegment_022_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 3847 68 = [12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3847 34 34, g32p_row03_traceSegment_022_3847_0034, g32p_row03_traceSegment_022_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 3780 135 = [21] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3780 67 68, g32p_row03_traceSegment_022_3780_0067, g32p_row03_traceSegment_022_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 3915 16 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3931 8 9, g32p_row03_traceSegment_022_3931_0008, g32p_row03_traceSegment_022_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 3915 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3915 16 17, g32p_row03_traceSegment_022_3915_0016, g32p_row03_traceSegment_022_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3948 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3948 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3948 8 9, g32p_row03_traceSegment_022_3948_0008, g32p_row03_traceSegment_022_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3973 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3965 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3965 8 9, g32p_row03_traceSegment_022_3965_0008, g32p_row03_traceSegment_022_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3948 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3948 17 17, g32p_row03_traceSegment_022_3948_0017, g32p_row03_traceSegment_022_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 3915 67 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3915 33 34, g32p_row03_traceSegment_022_3915_0033, g32p_row03_traceSegment_022_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3982 8 9, g32p_row03_traceSegment_022_3982_0008, g32p_row03_traceSegment_022_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3999 8 9, g32p_row03_traceSegment_022_3999_0008, g32p_row03_traceSegment_022_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3982 17 17, g32p_row03_traceSegment_022_3982_0017, g32p_row03_traceSegment_022_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4016 8 9, g32p_row03_traceSegment_022_4016_0008, g32p_row03_traceSegment_022_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4033 8 9, g32p_row03_traceSegment_022_4033_0008, g32p_row03_traceSegment_022_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4016 17 17, g32p_row03_traceSegment_022_4016_0017, g32p_row03_traceSegment_022_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3982 34 34, g32p_row03_traceSegment_022_3982_0034, g32p_row03_traceSegment_022_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 3915 135 = [6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3915 67 68, g32p_row03_traceSegment_022_3915_0067, g32p_row03_traceSegment_022_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 3780 270 = [27] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3780 135 135, g32p_row03_traceSegment_022_3780_0135, g32p_row03_traceSegment_022_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4066 8 9, g32p_row03_traceSegment_022_4066_0008, g32p_row03_traceSegment_022_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4050 16 17, g32p_row03_traceSegment_022_4050_0016, g32p_row03_traceSegment_022_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4091 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4083 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4083 8 9, g32p_row03_traceSegment_022_4083_0008, g32p_row03_traceSegment_022_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4100 8 9, g32p_row03_traceSegment_022_4100_0008, g32p_row03_traceSegment_022_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 4083 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4083 17 17, g32p_row03_traceSegment_022_4083_0017, g32p_row03_traceSegment_022_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 4050 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4050 33 34, g32p_row03_traceSegment_022_4050_0033, g32p_row03_traceSegment_022_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4117 8 9, g32p_row03_traceSegment_022_4117_0008, g32p_row03_traceSegment_022_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4134 8 9, g32p_row03_traceSegment_022_4134_0008, g32p_row03_traceSegment_022_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4117 17 17, g32p_row03_traceSegment_022_4117_0017, g32p_row03_traceSegment_022_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4151 8 9, g32p_row03_traceSegment_022_4151_0008, g32p_row03_traceSegment_022_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4168 8 9, g32p_row03_traceSegment_022_4168_0008, g32p_row03_traceSegment_022_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4151 17 17, g32p_row03_traceSegment_022_4151_0017, g32p_row03_traceSegment_022_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4117 34 34, g32p_row03_traceSegment_022_4117_0034, g32p_row03_traceSegment_022_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 4050 135 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4050 67 68, g32p_row03_traceSegment_022_4050_0067, g32p_row03_traceSegment_022_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_022 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4201 8 9, g32p_row03_traceSegment_022_4201_0008, g32p_row03_traceSegment_022_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_022 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4185 16 17, g32p_row03_traceSegment_022_4185_0016, g32p_row03_traceSegment_022_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4218 8 9, g32p_row03_traceSegment_022_4218_0008, g32p_row03_traceSegment_022_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4235 8 9, g32p_row03_traceSegment_022_4235_0008, g32p_row03_traceSegment_022_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4218 17 17, g32p_row03_traceSegment_022_4218_0017, g32p_row03_traceSegment_022_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_022 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4185 33 34, g32p_row03_traceSegment_022_4185_0033, g32p_row03_traceSegment_022_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4252 8 9, g32p_row03_traceSegment_022_4252_0008, g32p_row03_traceSegment_022_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4269 8 9, g32p_row03_traceSegment_022_4269_0008, g32p_row03_traceSegment_022_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4252 17 17, g32p_row03_traceSegment_022_4252_0017, g32p_row03_traceSegment_022_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4286 8 9, g32p_row03_traceSegment_022_4286_0008, g32p_row03_traceSegment_022_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_022 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_022 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_022_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_022 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4303 8 9, g32p_row03_traceSegment_022_4303_0008, g32p_row03_traceSegment_022_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_022 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4286 17 17, g32p_row03_traceSegment_022_4286_0017, g32p_row03_traceSegment_022_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_022 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4252 34 34, g32p_row03_traceSegment_022_4252_0034, g32p_row03_traceSegment_022_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_022 4185 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4185 67 68, g32p_row03_traceSegment_022_4185_0067, g32p_row03_traceSegment_022_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_022_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_022 4050 270 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 4050 135 135, g32p_row03_traceSegment_022_4050_0135, g32p_row03_traceSegment_022_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_022 3780 540 = [29] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3780 270 270, g32p_row03_traceSegment_022_3780_0270, g32p_row03_traceSegment_022_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_022_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_022 3240 1080 = [39] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 3240 540 540, g32p_row03_traceSegment_022_3240_0540, g32p_row03_traceSegment_022_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_022_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_022 2160 2160 = [101] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 2160 1080 1080, g32p_row03_traceSegment_022_2160_1080, g32p_row03_traceSegment_022_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_022_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_022 0 4320 = [144] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_022 0 2160 2160, g32p_row03_traceSegment_022_0000_2160, g32p_row03_traceSegment_022_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_022 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 22 = [144] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_022_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_024 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 24 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_024_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 16 8 9, g32p_row03_traceSegment_024_0016_0008, g32p_row03_traceSegment_024_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 0 16 17, g32p_row03_traceSegment_024_0000_0016, g32p_row03_traceSegment_024_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 33 8 9, g32p_row03_traceSegment_024_0033_0008, g32p_row03_traceSegment_024_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 50 8 9, g32p_row03_traceSegment_024_0050_0008, g32p_row03_traceSegment_024_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 33 17 17, g32p_row03_traceSegment_024_0033_0017, g32p_row03_traceSegment_024_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 0 33 34, g32p_row03_traceSegment_024_0000_0033, g32p_row03_traceSegment_024_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 67 8 9, g32p_row03_traceSegment_024_0067_0008, g32p_row03_traceSegment_024_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 84 8 9, g32p_row03_traceSegment_024_0084_0008, g32p_row03_traceSegment_024_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 67 17 17, g32p_row03_traceSegment_024_0067_0017, g32p_row03_traceSegment_024_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 101 8 9, g32p_row03_traceSegment_024_0101_0008, g32p_row03_traceSegment_024_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 118 8 9, g32p_row03_traceSegment_024_0118_0008, g32p_row03_traceSegment_024_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 101 17 17, g32p_row03_traceSegment_024_0101_0017, g32p_row03_traceSegment_024_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 67 34 34, g32p_row03_traceSegment_024_0067_0034, g32p_row03_traceSegment_024_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 0 67 68, g32p_row03_traceSegment_024_0000_0067, g32p_row03_traceSegment_024_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 151 8 9, g32p_row03_traceSegment_024_0151_0008, g32p_row03_traceSegment_024_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 135 16 17, g32p_row03_traceSegment_024_0135_0016, g32p_row03_traceSegment_024_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 168 8 9, g32p_row03_traceSegment_024_0168_0008, g32p_row03_traceSegment_024_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 185 8 9, g32p_row03_traceSegment_024_0185_0008, g32p_row03_traceSegment_024_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 168 17 17, g32p_row03_traceSegment_024_0168_0017, g32p_row03_traceSegment_024_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 135 33 34, g32p_row03_traceSegment_024_0135_0033, g32p_row03_traceSegment_024_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 202 8 9, g32p_row03_traceSegment_024_0202_0008, g32p_row03_traceSegment_024_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 219 8 9, g32p_row03_traceSegment_024_0219_0008, g32p_row03_traceSegment_024_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 202 17 17, g32p_row03_traceSegment_024_0202_0017, g32p_row03_traceSegment_024_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 236 8 9, g32p_row03_traceSegment_024_0236_0008, g32p_row03_traceSegment_024_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 253 8 9, g32p_row03_traceSegment_024_0253_0008, g32p_row03_traceSegment_024_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 236 17 17, g32p_row03_traceSegment_024_0236_0017, g32p_row03_traceSegment_024_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 202 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 202 34 34, g32p_row03_traceSegment_024_0202_0034, g32p_row03_traceSegment_024_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 135 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 135 67 68, g32p_row03_traceSegment_024_0135_0067, g32p_row03_traceSegment_024_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 0 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 0 135 135, g32p_row03_traceSegment_024_0000_0135, g32p_row03_traceSegment_024_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 286 8 9, g32p_row03_traceSegment_024_0286_0008, g32p_row03_traceSegment_024_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 270 16 17, g32p_row03_traceSegment_024_0270_0016, g32p_row03_traceSegment_024_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 303 8 9, g32p_row03_traceSegment_024_0303_0008, g32p_row03_traceSegment_024_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 320 8 9, g32p_row03_traceSegment_024_0320_0008, g32p_row03_traceSegment_024_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 303 17 17, g32p_row03_traceSegment_024_0303_0017, g32p_row03_traceSegment_024_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 270 33 34, g32p_row03_traceSegment_024_0270_0033, g32p_row03_traceSegment_024_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 337 8 9, g32p_row03_traceSegment_024_0337_0008, g32p_row03_traceSegment_024_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 354 8 9, g32p_row03_traceSegment_024_0354_0008, g32p_row03_traceSegment_024_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 337 17 17, g32p_row03_traceSegment_024_0337_0017, g32p_row03_traceSegment_024_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 371 8 9, g32p_row03_traceSegment_024_0371_0008, g32p_row03_traceSegment_024_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 388 8 9, g32p_row03_traceSegment_024_0388_0008, g32p_row03_traceSegment_024_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 371 17 17, g32p_row03_traceSegment_024_0371_0017, g32p_row03_traceSegment_024_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 337 34 34, g32p_row03_traceSegment_024_0337_0034, g32p_row03_traceSegment_024_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 270 67 68, g32p_row03_traceSegment_024_0270_0067, g32p_row03_traceSegment_024_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 421 8 9, g32p_row03_traceSegment_024_0421_0008, g32p_row03_traceSegment_024_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 405 16 17, g32p_row03_traceSegment_024_0405_0016, g32p_row03_traceSegment_024_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 438 8 9, g32p_row03_traceSegment_024_0438_0008, g32p_row03_traceSegment_024_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 455 8 9, g32p_row03_traceSegment_024_0455_0008, g32p_row03_traceSegment_024_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 438 17 17, g32p_row03_traceSegment_024_0438_0017, g32p_row03_traceSegment_024_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 405 33 34, g32p_row03_traceSegment_024_0405_0033, g32p_row03_traceSegment_024_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 472 8 9, g32p_row03_traceSegment_024_0472_0008, g32p_row03_traceSegment_024_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 489 8 9, g32p_row03_traceSegment_024_0489_0008, g32p_row03_traceSegment_024_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 472 17 17, g32p_row03_traceSegment_024_0472_0017, g32p_row03_traceSegment_024_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 506 8 9, g32p_row03_traceSegment_024_0506_0008, g32p_row03_traceSegment_024_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 523 8 9, g32p_row03_traceSegment_024_0523_0008, g32p_row03_traceSegment_024_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 506 17 17, g32p_row03_traceSegment_024_0506_0017, g32p_row03_traceSegment_024_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 472 34 34, g32p_row03_traceSegment_024_0472_0034, g32p_row03_traceSegment_024_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 405 67 68, g32p_row03_traceSegment_024_0405_0067, g32p_row03_traceSegment_024_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 270 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 270 135 135, g32p_row03_traceSegment_024_0270_0135, g32p_row03_traceSegment_024_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_024 0 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 0 270 270, g32p_row03_traceSegment_024_0000_0270, g32p_row03_traceSegment_024_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 556 8 9, g32p_row03_traceSegment_024_0556_0008, g32p_row03_traceSegment_024_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 540 16 17, g32p_row03_traceSegment_024_0540_0016, g32p_row03_traceSegment_024_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 573 8 9, g32p_row03_traceSegment_024_0573_0008, g32p_row03_traceSegment_024_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 590 8 9, g32p_row03_traceSegment_024_0590_0008, g32p_row03_traceSegment_024_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 573 17 17, g32p_row03_traceSegment_024_0573_0017, g32p_row03_traceSegment_024_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 540 33 34, g32p_row03_traceSegment_024_0540_0033, g32p_row03_traceSegment_024_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 607 8 9, g32p_row03_traceSegment_024_0607_0008, g32p_row03_traceSegment_024_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 624 8 9, g32p_row03_traceSegment_024_0624_0008, g32p_row03_traceSegment_024_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 607 17 17, g32p_row03_traceSegment_024_0607_0017, g32p_row03_traceSegment_024_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 641 8 9, g32p_row03_traceSegment_024_0641_0008, g32p_row03_traceSegment_024_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 658 8 9, g32p_row03_traceSegment_024_0658_0008, g32p_row03_traceSegment_024_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 641 17 17, g32p_row03_traceSegment_024_0641_0017, g32p_row03_traceSegment_024_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 607 34 34, g32p_row03_traceSegment_024_0607_0034, g32p_row03_traceSegment_024_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 540 67 68, g32p_row03_traceSegment_024_0540_0067, g32p_row03_traceSegment_024_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 691 8 9, g32p_row03_traceSegment_024_0691_0008, g32p_row03_traceSegment_024_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 675 16 17, g32p_row03_traceSegment_024_0675_0016, g32p_row03_traceSegment_024_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 708 8 9, g32p_row03_traceSegment_024_0708_0008, g32p_row03_traceSegment_024_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 725 8 9, g32p_row03_traceSegment_024_0725_0008, g32p_row03_traceSegment_024_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 708 17 17, g32p_row03_traceSegment_024_0708_0017, g32p_row03_traceSegment_024_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 675 33 34, g32p_row03_traceSegment_024_0675_0033, g32p_row03_traceSegment_024_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 742 8 9, g32p_row03_traceSegment_024_0742_0008, g32p_row03_traceSegment_024_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 759 8 9, g32p_row03_traceSegment_024_0759_0008, g32p_row03_traceSegment_024_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 742 17 17, g32p_row03_traceSegment_024_0742_0017, g32p_row03_traceSegment_024_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 776 8 9, g32p_row03_traceSegment_024_0776_0008, g32p_row03_traceSegment_024_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 793 8 9, g32p_row03_traceSegment_024_0793_0008, g32p_row03_traceSegment_024_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 776 17 17, g32p_row03_traceSegment_024_0776_0017, g32p_row03_traceSegment_024_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 742 34 34, g32p_row03_traceSegment_024_0742_0034, g32p_row03_traceSegment_024_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 675 67 68, g32p_row03_traceSegment_024_0675_0067, g32p_row03_traceSegment_024_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 540 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 540 135 135, g32p_row03_traceSegment_024_0540_0135, g32p_row03_traceSegment_024_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 826 8 9, g32p_row03_traceSegment_024_0826_0008, g32p_row03_traceSegment_024_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 810 16 17, g32p_row03_traceSegment_024_0810_0016, g32p_row03_traceSegment_024_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 843 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 843 8 9, g32p_row03_traceSegment_024_0843_0008, g32p_row03_traceSegment_024_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 860 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 860 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 860 8 9, g32p_row03_traceSegment_024_0860_0008, g32p_row03_traceSegment_024_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 843 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 843 17 17, g32p_row03_traceSegment_024_0843_0017, g32p_row03_traceSegment_024_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 810 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 810 33 34, g32p_row03_traceSegment_024_0810_0033, g32p_row03_traceSegment_024_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 877 8 9, g32p_row03_traceSegment_024_0877_0008, g32p_row03_traceSegment_024_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 894 8 9, g32p_row03_traceSegment_024_0894_0008, g32p_row03_traceSegment_024_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 877 17 17, g32p_row03_traceSegment_024_0877_0017, g32p_row03_traceSegment_024_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 911 8 9, g32p_row03_traceSegment_024_0911_0008, g32p_row03_traceSegment_024_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 928 8 9, g32p_row03_traceSegment_024_0928_0008, g32p_row03_traceSegment_024_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 911 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 911 17 17, g32p_row03_traceSegment_024_0911_0017, g32p_row03_traceSegment_024_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 877 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 877 34 34, g32p_row03_traceSegment_024_0877_0034, g32p_row03_traceSegment_024_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 810 135 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 810 67 68, g32p_row03_traceSegment_024_0810_0067, g32p_row03_traceSegment_024_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 961 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 961 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 961 8 9, g32p_row03_traceSegment_024_0961_0008, g32p_row03_traceSegment_024_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 945 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 945 16 17, g32p_row03_traceSegment_024_0945_0016, g32p_row03_traceSegment_024_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 986 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 978 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 978 8 9, g32p_row03_traceSegment_024_0978_0008, g32p_row03_traceSegment_024_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 995 8 9, g32p_row03_traceSegment_024_0995_0008, g32p_row03_traceSegment_024_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 978 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 978 17 17, g32p_row03_traceSegment_024_0978_0017, g32p_row03_traceSegment_024_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 945 67 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 945 33 34, g32p_row03_traceSegment_024_0945_0033, g32p_row03_traceSegment_024_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1012 8 9, g32p_row03_traceSegment_024_1012_0008, g32p_row03_traceSegment_024_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1029 8 9, g32p_row03_traceSegment_024_1029_0008, g32p_row03_traceSegment_024_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1012 17 17, g32p_row03_traceSegment_024_1012_0017, g32p_row03_traceSegment_024_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1054 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1046 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1046 8 9, g32p_row03_traceSegment_024_1046_0008, g32p_row03_traceSegment_024_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1063 8 9, g32p_row03_traceSegment_024_1063_0008, g32p_row03_traceSegment_024_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1046 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1046 17 17, g32p_row03_traceSegment_024_1046_0017, g32p_row03_traceSegment_024_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 1012 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1012 34 34, g32p_row03_traceSegment_024_1012_0034, g32p_row03_traceSegment_024_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 945 135 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 945 67 68, g32p_row03_traceSegment_024_0945_0067, g32p_row03_traceSegment_024_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 810 270 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 810 135 135, g32p_row03_traceSegment_024_0810_0135, g32p_row03_traceSegment_024_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_024 540 540 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 540 270 270, g32p_row03_traceSegment_024_0540_0270, g32p_row03_traceSegment_024_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_024 0 1080 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 0 540 540, g32p_row03_traceSegment_024_0000_0540, g32p_row03_traceSegment_024_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1096 8 9, g32p_row03_traceSegment_024_1096_0008, g32p_row03_traceSegment_024_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1080 16 17, g32p_row03_traceSegment_024_1080_0016, g32p_row03_traceSegment_024_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1113 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1121 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1113 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1113 8 9, g32p_row03_traceSegment_024_1113_0008, g32p_row03_traceSegment_024_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1130 8 9, g32p_row03_traceSegment_024_1130_0008, g32p_row03_traceSegment_024_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1113 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1113 17 17, g32p_row03_traceSegment_024_1113_0017, g32p_row03_traceSegment_024_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 1080 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1080 33 34, g32p_row03_traceSegment_024_1080_0033, g32p_row03_traceSegment_024_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1147 8 9, g32p_row03_traceSegment_024_1147_0008, g32p_row03_traceSegment_024_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1164 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1164 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1164 8 9, g32p_row03_traceSegment_024_1164_0008, g32p_row03_traceSegment_024_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1147 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1147 17 17, g32p_row03_traceSegment_024_1147_0017, g32p_row03_traceSegment_024_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1189 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1181 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1181 8 9, g32p_row03_traceSegment_024_1181_0008, g32p_row03_traceSegment_024_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1198 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1198 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1198 8 9, g32p_row03_traceSegment_024_1198_0008, g32p_row03_traceSegment_024_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1181 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1181 17 17, g32p_row03_traceSegment_024_1181_0017, g32p_row03_traceSegment_024_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 1147 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1147 34 34, g32p_row03_traceSegment_024_1147_0034, g32p_row03_traceSegment_024_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 1080 135 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1080 67 68, g32p_row03_traceSegment_024_1080_0067, g32p_row03_traceSegment_024_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1231 8 9, g32p_row03_traceSegment_024_1231_0008, g32p_row03_traceSegment_024_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1215 16 17, g32p_row03_traceSegment_024_1215_0016, g32p_row03_traceSegment_024_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1248 8 9, g32p_row03_traceSegment_024_1248_0008, g32p_row03_traceSegment_024_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1265 8 9, g32p_row03_traceSegment_024_1265_0008, g32p_row03_traceSegment_024_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1248 17 17, g32p_row03_traceSegment_024_1248_0017, g32p_row03_traceSegment_024_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1215 33 34, g32p_row03_traceSegment_024_1215_0033, g32p_row03_traceSegment_024_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1282 8 9, g32p_row03_traceSegment_024_1282_0008, g32p_row03_traceSegment_024_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1299 8 9, g32p_row03_traceSegment_024_1299_0008, g32p_row03_traceSegment_024_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1282 17 17, g32p_row03_traceSegment_024_1282_0017, g32p_row03_traceSegment_024_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1316 8 9, g32p_row03_traceSegment_024_1316_0008, g32p_row03_traceSegment_024_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1333 8 9, g32p_row03_traceSegment_024_1333_0008, g32p_row03_traceSegment_024_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1316 17 17, g32p_row03_traceSegment_024_1316_0017, g32p_row03_traceSegment_024_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1282 34 34, g32p_row03_traceSegment_024_1282_0034, g32p_row03_traceSegment_024_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1215 67 68, g32p_row03_traceSegment_024_1215_0067, g32p_row03_traceSegment_024_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 1080 270 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1080 135 135, g32p_row03_traceSegment_024_1080_0135, g32p_row03_traceSegment_024_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1366 8 9, g32p_row03_traceSegment_024_1366_0008, g32p_row03_traceSegment_024_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1350 16 17, g32p_row03_traceSegment_024_1350_0016, g32p_row03_traceSegment_024_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1383 8 9, g32p_row03_traceSegment_024_1383_0008, g32p_row03_traceSegment_024_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1400 8 9, g32p_row03_traceSegment_024_1400_0008, g32p_row03_traceSegment_024_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1383 17 17, g32p_row03_traceSegment_024_1383_0017, g32p_row03_traceSegment_024_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1350 33 34, g32p_row03_traceSegment_024_1350_0033, g32p_row03_traceSegment_024_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1417 8 9, g32p_row03_traceSegment_024_1417_0008, g32p_row03_traceSegment_024_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1434 8 9, g32p_row03_traceSegment_024_1434_0008, g32p_row03_traceSegment_024_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1417 17 17, g32p_row03_traceSegment_024_1417_0017, g32p_row03_traceSegment_024_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1451 8 9, g32p_row03_traceSegment_024_1451_0008, g32p_row03_traceSegment_024_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1468 8 9, g32p_row03_traceSegment_024_1468_0008, g32p_row03_traceSegment_024_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1451 17 17, g32p_row03_traceSegment_024_1451_0017, g32p_row03_traceSegment_024_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1417 34 34, g32p_row03_traceSegment_024_1417_0034, g32p_row03_traceSegment_024_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 1350 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1350 67 68, g32p_row03_traceSegment_024_1350_0067, g32p_row03_traceSegment_024_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1501 8 9, g32p_row03_traceSegment_024_1501_0008, g32p_row03_traceSegment_024_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1485 16 17, g32p_row03_traceSegment_024_1485_0016, g32p_row03_traceSegment_024_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1518 8 9, g32p_row03_traceSegment_024_1518_0008, g32p_row03_traceSegment_024_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1535 8 9, g32p_row03_traceSegment_024_1535_0008, g32p_row03_traceSegment_024_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1518 17 17, g32p_row03_traceSegment_024_1518_0017, g32p_row03_traceSegment_024_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1485 33 34, g32p_row03_traceSegment_024_1485_0033, g32p_row03_traceSegment_024_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1552 8 9, g32p_row03_traceSegment_024_1552_0008, g32p_row03_traceSegment_024_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1569 8 9, g32p_row03_traceSegment_024_1569_0008, g32p_row03_traceSegment_024_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1552 17 17, g32p_row03_traceSegment_024_1552_0017, g32p_row03_traceSegment_024_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1586 8 9, g32p_row03_traceSegment_024_1586_0008, g32p_row03_traceSegment_024_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1603 8 9, g32p_row03_traceSegment_024_1603_0008, g32p_row03_traceSegment_024_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1586 17 17, g32p_row03_traceSegment_024_1586_0017, g32p_row03_traceSegment_024_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1552 34 34, g32p_row03_traceSegment_024_1552_0034, g32p_row03_traceSegment_024_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 1485 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1485 67 68, g32p_row03_traceSegment_024_1485_0067, g32p_row03_traceSegment_024_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 1350 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1350 135 135, g32p_row03_traceSegment_024_1350_0135, g32p_row03_traceSegment_024_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_024 1080 540 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1080 270 270, g32p_row03_traceSegment_024_1080_0270, g32p_row03_traceSegment_024_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1636 8 9, g32p_row03_traceSegment_024_1636_0008, g32p_row03_traceSegment_024_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1620 16 17, g32p_row03_traceSegment_024_1620_0016, g32p_row03_traceSegment_024_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1653 8 9, g32p_row03_traceSegment_024_1653_0008, g32p_row03_traceSegment_024_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1670 8 9, g32p_row03_traceSegment_024_1670_0008, g32p_row03_traceSegment_024_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1653 17 17, g32p_row03_traceSegment_024_1653_0017, g32p_row03_traceSegment_024_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1620 33 34, g32p_row03_traceSegment_024_1620_0033, g32p_row03_traceSegment_024_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1687 8 9, g32p_row03_traceSegment_024_1687_0008, g32p_row03_traceSegment_024_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1704 8 9, g32p_row03_traceSegment_024_1704_0008, g32p_row03_traceSegment_024_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1687 17 17, g32p_row03_traceSegment_024_1687_0017, g32p_row03_traceSegment_024_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1721 8 9, g32p_row03_traceSegment_024_1721_0008, g32p_row03_traceSegment_024_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1738 8 9, g32p_row03_traceSegment_024_1738_0008, g32p_row03_traceSegment_024_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1721 17 17, g32p_row03_traceSegment_024_1721_0017, g32p_row03_traceSegment_024_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1687 34 34, g32p_row03_traceSegment_024_1687_0034, g32p_row03_traceSegment_024_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 1620 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1620 67 68, g32p_row03_traceSegment_024_1620_0067, g32p_row03_traceSegment_024_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1771 8 9, g32p_row03_traceSegment_024_1771_0008, g32p_row03_traceSegment_024_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1755 16 17, g32p_row03_traceSegment_024_1755_0016, g32p_row03_traceSegment_024_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1788 8 9, g32p_row03_traceSegment_024_1788_0008, g32p_row03_traceSegment_024_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1805 8 9, g32p_row03_traceSegment_024_1805_0008, g32p_row03_traceSegment_024_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1788 17 17, g32p_row03_traceSegment_024_1788_0017, g32p_row03_traceSegment_024_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1755 33 34, g32p_row03_traceSegment_024_1755_0033, g32p_row03_traceSegment_024_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1822 8 9, g32p_row03_traceSegment_024_1822_0008, g32p_row03_traceSegment_024_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1839 8 9, g32p_row03_traceSegment_024_1839_0008, g32p_row03_traceSegment_024_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1822 17 17, g32p_row03_traceSegment_024_1822_0017, g32p_row03_traceSegment_024_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1856 8 9, g32p_row03_traceSegment_024_1856_0008, g32p_row03_traceSegment_024_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1873 8 9, g32p_row03_traceSegment_024_1873_0008, g32p_row03_traceSegment_024_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1856 17 17, g32p_row03_traceSegment_024_1856_0017, g32p_row03_traceSegment_024_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1822 34 34, g32p_row03_traceSegment_024_1822_0034, g32p_row03_traceSegment_024_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 1755 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1755 67 68, g32p_row03_traceSegment_024_1755_0067, g32p_row03_traceSegment_024_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 1620 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1620 135 135, g32p_row03_traceSegment_024_1620_0135, g32p_row03_traceSegment_024_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1906 8 9, g32p_row03_traceSegment_024_1906_0008, g32p_row03_traceSegment_024_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1890 16 17, g32p_row03_traceSegment_024_1890_0016, g32p_row03_traceSegment_024_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1923 8 9, g32p_row03_traceSegment_024_1923_0008, g32p_row03_traceSegment_024_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1940 8 9, g32p_row03_traceSegment_024_1940_0008, g32p_row03_traceSegment_024_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1923 17 17, g32p_row03_traceSegment_024_1923_0017, g32p_row03_traceSegment_024_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1890 33 34, g32p_row03_traceSegment_024_1890_0033, g32p_row03_traceSegment_024_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1957 8 9, g32p_row03_traceSegment_024_1957_0008, g32p_row03_traceSegment_024_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1974 8 9, g32p_row03_traceSegment_024_1974_0008, g32p_row03_traceSegment_024_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1957 17 17, g32p_row03_traceSegment_024_1957_0017, g32p_row03_traceSegment_024_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1991 8 9, g32p_row03_traceSegment_024_1991_0008, g32p_row03_traceSegment_024_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2008 8 9, g32p_row03_traceSegment_024_2008_0008, g32p_row03_traceSegment_024_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1991 17 17, g32p_row03_traceSegment_024_1991_0017, g32p_row03_traceSegment_024_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1957 34 34, g32p_row03_traceSegment_024_1957_0034, g32p_row03_traceSegment_024_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1890 67 68, g32p_row03_traceSegment_024_1890_0067, g32p_row03_traceSegment_024_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 2025 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2041 8 9, g32p_row03_traceSegment_024_2041_0008, g32p_row03_traceSegment_024_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 2025 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2025 16 17, g32p_row03_traceSegment_024_2025_0016, g32p_row03_traceSegment_024_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2058 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2058 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2058 8 9, g32p_row03_traceSegment_024_2058_0008, g32p_row03_traceSegment_024_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2075 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2083 9 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2075 17 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2075 8 9, g32p_row03_traceSegment_024_2075_0008, g32p_row03_traceSegment_024_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2058 34 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2058 17 17, g32p_row03_traceSegment_024_2058_0017, g32p_row03_traceSegment_024_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 2025 67 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2025 33 34, g32p_row03_traceSegment_024_2025_0033, g32p_row03_traceSegment_024_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2100 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2092 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2092 8 9, g32p_row03_traceSegment_024_2092_0008, g32p_row03_traceSegment_024_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2109 8 9, g32p_row03_traceSegment_024_2109_0008, g32p_row03_traceSegment_024_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2092 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2092 17 17, g32p_row03_traceSegment_024_2092_0017, g32p_row03_traceSegment_024_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2134 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2126 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2126 8 9, g32p_row03_traceSegment_024_2126_0008, g32p_row03_traceSegment_024_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2143 8 9, g32p_row03_traceSegment_024_2143_0008, g32p_row03_traceSegment_024_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2126 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2126 17 17, g32p_row03_traceSegment_024_2126_0017, g32p_row03_traceSegment_024_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 2092 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2092 34 34, g32p_row03_traceSegment_024_2092_0034, g32p_row03_traceSegment_024_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 2025 135 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2025 67 68, g32p_row03_traceSegment_024_2025_0067, g32p_row03_traceSegment_024_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 1890 270 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1890 135 135, g32p_row03_traceSegment_024_1890_0135, g32p_row03_traceSegment_024_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_024 1620 540 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1620 270 270, g32p_row03_traceSegment_024_1620_0270, g32p_row03_traceSegment_024_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_024_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_024 1080 1080 = [12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 1080 540 540, g32p_row03_traceSegment_024_1080_0540, g32p_row03_traceSegment_024_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_024 0 2160 = [17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 0 1080 1080, g32p_row03_traceSegment_024_0000_1080, g32p_row03_traceSegment_024_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 2160 16 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2176 8 9, g32p_row03_traceSegment_024_2176_0008, g32p_row03_traceSegment_024_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 2160 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2160 16 17, g32p_row03_traceSegment_024_2160_0016, g32p_row03_traceSegment_024_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2193 8 9, g32p_row03_traceSegment_024_2193_0008, g32p_row03_traceSegment_024_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2210 8 9, g32p_row03_traceSegment_024_2210_0008, g32p_row03_traceSegment_024_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2193 17 17, g32p_row03_traceSegment_024_2193_0017, g32p_row03_traceSegment_024_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 2160 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2160 33 34, g32p_row03_traceSegment_024_2160_0033, g32p_row03_traceSegment_024_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2227 8 9, g32p_row03_traceSegment_024_2227_0008, g32p_row03_traceSegment_024_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2244 8 9, g32p_row03_traceSegment_024_2244_0008, g32p_row03_traceSegment_024_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2227 17 17, g32p_row03_traceSegment_024_2227_0017, g32p_row03_traceSegment_024_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2261 8 9, g32p_row03_traceSegment_024_2261_0008, g32p_row03_traceSegment_024_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2278 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2278 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2278 8 9, g32p_row03_traceSegment_024_2278_0008, g32p_row03_traceSegment_024_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2261 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2261 17 17, g32p_row03_traceSegment_024_2261_0017, g32p_row03_traceSegment_024_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 2227 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2227 34 34, g32p_row03_traceSegment_024_2227_0034, g32p_row03_traceSegment_024_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 2160 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2160 67 68, g32p_row03_traceSegment_024_2160_0067, g32p_row03_traceSegment_024_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 2295 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2311 8 9, g32p_row03_traceSegment_024_2311_0008, g32p_row03_traceSegment_024_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 2295 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2295 16 17, g32p_row03_traceSegment_024_2295_0016, g32p_row03_traceSegment_024_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2328 8 9, g32p_row03_traceSegment_024_2328_0008, g32p_row03_traceSegment_024_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2353 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2345 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2345 8 9, g32p_row03_traceSegment_024_2345_0008, g32p_row03_traceSegment_024_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2328 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2328 17 17, g32p_row03_traceSegment_024_2328_0017, g32p_row03_traceSegment_024_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 2295 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2295 33 34, g32p_row03_traceSegment_024_2295_0033, g32p_row03_traceSegment_024_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2370 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2362 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2362 8 9, g32p_row03_traceSegment_024_2362_0008, g32p_row03_traceSegment_024_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2379 8 9, g32p_row03_traceSegment_024_2379_0008, g32p_row03_traceSegment_024_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2362 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2362 17 17, g32p_row03_traceSegment_024_2362_0017, g32p_row03_traceSegment_024_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2404 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2396 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2396 8 9, g32p_row03_traceSegment_024_2396_0008, g32p_row03_traceSegment_024_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2413 8 9, g32p_row03_traceSegment_024_2413_0008, g32p_row03_traceSegment_024_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2396 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2396 17 17, g32p_row03_traceSegment_024_2396_0017, g32p_row03_traceSegment_024_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 2362 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2362 34 34, g32p_row03_traceSegment_024_2362_0034, g32p_row03_traceSegment_024_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 2295 135 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2295 67 68, g32p_row03_traceSegment_024_2295_0067, g32p_row03_traceSegment_024_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 2160 270 = [7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2160 135 135, g32p_row03_traceSegment_024_2160_0135, g32p_row03_traceSegment_024_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2446 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2446 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2446 8 9, g32p_row03_traceSegment_024_2446_0008, g32p_row03_traceSegment_024_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 2430 33 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2430 16 17, g32p_row03_traceSegment_024_2430_0016, g32p_row03_traceSegment_024_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2463 8 9, g32p_row03_traceSegment_024_2463_0008, g32p_row03_traceSegment_024_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2480 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2480 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2480 8 9, g32p_row03_traceSegment_024_2480_0008, g32p_row03_traceSegment_024_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2463 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2463 17 17, g32p_row03_traceSegment_024_2463_0017, g32p_row03_traceSegment_024_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 2430 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2430 33 34, g32p_row03_traceSegment_024_2430_0033, g32p_row03_traceSegment_024_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2497 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2505 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2497 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2497 8 9, g32p_row03_traceSegment_024_2497_0008, g32p_row03_traceSegment_024_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2522 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2514 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2514 8 9, g32p_row03_traceSegment_024_2514_0008, g32p_row03_traceSegment_024_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2497 34 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2497 17 17, g32p_row03_traceSegment_024_2497_0017, g32p_row03_traceSegment_024_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2531 8 9, g32p_row03_traceSegment_024_2531_0008, g32p_row03_traceSegment_024_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2548 8 9, g32p_row03_traceSegment_024_2548_0008, g32p_row03_traceSegment_024_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2531 17 17, g32p_row03_traceSegment_024_2531_0017, g32p_row03_traceSegment_024_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 2497 68 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2497 34 34, g32p_row03_traceSegment_024_2497_0034, g32p_row03_traceSegment_024_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 2430 135 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2430 67 68, g32p_row03_traceSegment_024_2430_0067, g32p_row03_traceSegment_024_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 2565 16 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2589 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2581 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2581 8 9, g32p_row03_traceSegment_024_2581_0008, g32p_row03_traceSegment_024_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 2565 33 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2565 16 17, g32p_row03_traceSegment_024_2565_0016, g32p_row03_traceSegment_024_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2598 8 9, g32p_row03_traceSegment_024_2598_0008, g32p_row03_traceSegment_024_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2615 8 9, g32p_row03_traceSegment_024_2615_0008, g32p_row03_traceSegment_024_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2598 17 17, g32p_row03_traceSegment_024_2598_0017, g32p_row03_traceSegment_024_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 2565 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2565 33 34, g32p_row03_traceSegment_024_2565_0033, g32p_row03_traceSegment_024_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2640 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2632 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2632 8 9, g32p_row03_traceSegment_024_2632_0008, g32p_row03_traceSegment_024_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2649 8 9, g32p_row03_traceSegment_024_2649_0008, g32p_row03_traceSegment_024_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2632 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2632 17 17, g32p_row03_traceSegment_024_2632_0017, g32p_row03_traceSegment_024_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2666 8 9, g32p_row03_traceSegment_024_2666_0008, g32p_row03_traceSegment_024_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2683 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2683 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2683 8 9, g32p_row03_traceSegment_024_2683_0008, g32p_row03_traceSegment_024_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2666 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2666 17 17, g32p_row03_traceSegment_024_2666_0017, g32p_row03_traceSegment_024_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 2632 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2632 34 34, g32p_row03_traceSegment_024_2632_0034, g32p_row03_traceSegment_024_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 2565 135 = [4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2565 67 68, g32p_row03_traceSegment_024_2565_0067, g32p_row03_traceSegment_024_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 2430 270 = [9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2430 135 135, g32p_row03_traceSegment_024_2430_0135, g32p_row03_traceSegment_024_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_024 2160 540 = [16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2160 270 270, g32p_row03_traceSegment_024_2160_0270, g32p_row03_traceSegment_024_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2716 8 9, g32p_row03_traceSegment_024_2716_0008, g32p_row03_traceSegment_024_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2700 16 17, g32p_row03_traceSegment_024_2700_0016, g32p_row03_traceSegment_024_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2733 8 9, g32p_row03_traceSegment_024_2733_0008, g32p_row03_traceSegment_024_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2750 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2750 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2750 8 9, g32p_row03_traceSegment_024_2750_0008, g32p_row03_traceSegment_024_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2733 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2733 17 17, g32p_row03_traceSegment_024_2733_0017, g32p_row03_traceSegment_024_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 2700 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2700 33 34, g32p_row03_traceSegment_024_2700_0033, g32p_row03_traceSegment_024_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2767 8 9, g32p_row03_traceSegment_024_2767_0008, g32p_row03_traceSegment_024_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2784 8 9, g32p_row03_traceSegment_024_2784_0008, g32p_row03_traceSegment_024_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2767 17 17, g32p_row03_traceSegment_024_2767_0017, g32p_row03_traceSegment_024_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2801 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2801 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2801 8 9, g32p_row03_traceSegment_024_2801_0008, g32p_row03_traceSegment_024_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2818 8 9, g32p_row03_traceSegment_024_2818_0008, g32p_row03_traceSegment_024_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2801 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2801 17 17, g32p_row03_traceSegment_024_2801_0017, g32p_row03_traceSegment_024_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 2767 68 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2767 34 34, g32p_row03_traceSegment_024_2767_0034, g32p_row03_traceSegment_024_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 2700 135 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2700 67 68, g32p_row03_traceSegment_024_2700_0067, g32p_row03_traceSegment_024_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2851 8 9, g32p_row03_traceSegment_024_2851_0008, g32p_row03_traceSegment_024_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2835 16 17, g32p_row03_traceSegment_024_2835_0016, g32p_row03_traceSegment_024_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2868 8 9, g32p_row03_traceSegment_024_2868_0008, g32p_row03_traceSegment_024_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2885 8 9, g32p_row03_traceSegment_024_2885_0008, g32p_row03_traceSegment_024_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2868 17 17, g32p_row03_traceSegment_024_2868_0017, g32p_row03_traceSegment_024_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2835 33 34, g32p_row03_traceSegment_024_2835_0033, g32p_row03_traceSegment_024_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2902 8 9, g32p_row03_traceSegment_024_2902_0008, g32p_row03_traceSegment_024_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2919 8 9, g32p_row03_traceSegment_024_2919_0008, g32p_row03_traceSegment_024_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2902 17 17, g32p_row03_traceSegment_024_2902_0017, g32p_row03_traceSegment_024_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2936 8 9, g32p_row03_traceSegment_024_2936_0008, g32p_row03_traceSegment_024_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2953 8 9, g32p_row03_traceSegment_024_2953_0008, g32p_row03_traceSegment_024_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2936 17 17, g32p_row03_traceSegment_024_2936_0017, g32p_row03_traceSegment_024_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2902 34 34, g32p_row03_traceSegment_024_2902_0034, g32p_row03_traceSegment_024_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2835 67 68, g32p_row03_traceSegment_024_2835_0067, g32p_row03_traceSegment_024_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 2700 270 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2700 135 135, g32p_row03_traceSegment_024_2700_0135, g32p_row03_traceSegment_024_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2986 8 9, g32p_row03_traceSegment_024_2986_0008, g32p_row03_traceSegment_024_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2970 16 17, g32p_row03_traceSegment_024_2970_0016, g32p_row03_traceSegment_024_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3003 8 9, g32p_row03_traceSegment_024_3003_0008, g32p_row03_traceSegment_024_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3020 8 9, g32p_row03_traceSegment_024_3020_0008, g32p_row03_traceSegment_024_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3003 17 17, g32p_row03_traceSegment_024_3003_0017, g32p_row03_traceSegment_024_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2970 33 34, g32p_row03_traceSegment_024_2970_0033, g32p_row03_traceSegment_024_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3037 8 9, g32p_row03_traceSegment_024_3037_0008, g32p_row03_traceSegment_024_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3054 8 9, g32p_row03_traceSegment_024_3054_0008, g32p_row03_traceSegment_024_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3037 17 17, g32p_row03_traceSegment_024_3037_0017, g32p_row03_traceSegment_024_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3071 8 9, g32p_row03_traceSegment_024_3071_0008, g32p_row03_traceSegment_024_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3088 8 9, g32p_row03_traceSegment_024_3088_0008, g32p_row03_traceSegment_024_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3071 17 17, g32p_row03_traceSegment_024_3071_0017, g32p_row03_traceSegment_024_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3037 34 34, g32p_row03_traceSegment_024_3037_0034, g32p_row03_traceSegment_024_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2970 67 68, g32p_row03_traceSegment_024_2970_0067, g32p_row03_traceSegment_024_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3121 8 9, g32p_row03_traceSegment_024_3121_0008, g32p_row03_traceSegment_024_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3105 16 17, g32p_row03_traceSegment_024_3105_0016, g32p_row03_traceSegment_024_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3138 8 9, g32p_row03_traceSegment_024_3138_0008, g32p_row03_traceSegment_024_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3155 8 9, g32p_row03_traceSegment_024_3155_0008, g32p_row03_traceSegment_024_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3138 17 17, g32p_row03_traceSegment_024_3138_0017, g32p_row03_traceSegment_024_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3105 33 34, g32p_row03_traceSegment_024_3105_0033, g32p_row03_traceSegment_024_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3172 8 9, g32p_row03_traceSegment_024_3172_0008, g32p_row03_traceSegment_024_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3189 8 9, g32p_row03_traceSegment_024_3189_0008, g32p_row03_traceSegment_024_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3172 17 17, g32p_row03_traceSegment_024_3172_0017, g32p_row03_traceSegment_024_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3206 8 9, g32p_row03_traceSegment_024_3206_0008, g32p_row03_traceSegment_024_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3223 8 9, g32p_row03_traceSegment_024_3223_0008, g32p_row03_traceSegment_024_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3206 17 17, g32p_row03_traceSegment_024_3206_0017, g32p_row03_traceSegment_024_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3172 34 34, g32p_row03_traceSegment_024_3172_0034, g32p_row03_traceSegment_024_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 3105 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3105 67 68, g32p_row03_traceSegment_024_3105_0067, g32p_row03_traceSegment_024_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 2970 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2970 135 135, g32p_row03_traceSegment_024_2970_0135, g32p_row03_traceSegment_024_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_024 2700 540 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2700 270 270, g32p_row03_traceSegment_024_2700_0270, g32p_row03_traceSegment_024_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_024 2160 1080 = [18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2160 540 540, g32p_row03_traceSegment_024_2160_0540, g32p_row03_traceSegment_024_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3256 8 9, g32p_row03_traceSegment_024_3256_0008, g32p_row03_traceSegment_024_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3240 16 17, g32p_row03_traceSegment_024_3240_0016, g32p_row03_traceSegment_024_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3273 8 9, g32p_row03_traceSegment_024_3273_0008, g32p_row03_traceSegment_024_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3290 8 9, g32p_row03_traceSegment_024_3290_0008, g32p_row03_traceSegment_024_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3273 17 17, g32p_row03_traceSegment_024_3273_0017, g32p_row03_traceSegment_024_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3240 33 34, g32p_row03_traceSegment_024_3240_0033, g32p_row03_traceSegment_024_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3307 8 9, g32p_row03_traceSegment_024_3307_0008, g32p_row03_traceSegment_024_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3324 8 9, g32p_row03_traceSegment_024_3324_0008, g32p_row03_traceSegment_024_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3307 17 17, g32p_row03_traceSegment_024_3307_0017, g32p_row03_traceSegment_024_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3341 8 9, g32p_row03_traceSegment_024_3341_0008, g32p_row03_traceSegment_024_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3358 8 9, g32p_row03_traceSegment_024_3358_0008, g32p_row03_traceSegment_024_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3341 17 17, g32p_row03_traceSegment_024_3341_0017, g32p_row03_traceSegment_024_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3307 34 34, g32p_row03_traceSegment_024_3307_0034, g32p_row03_traceSegment_024_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 3240 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3240 67 68, g32p_row03_traceSegment_024_3240_0067, g32p_row03_traceSegment_024_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3391 8 9, g32p_row03_traceSegment_024_3391_0008, g32p_row03_traceSegment_024_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3375 16 17, g32p_row03_traceSegment_024_3375_0016, g32p_row03_traceSegment_024_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3408 8 9, g32p_row03_traceSegment_024_3408_0008, g32p_row03_traceSegment_024_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3425 8 9, g32p_row03_traceSegment_024_3425_0008, g32p_row03_traceSegment_024_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3408 17 17, g32p_row03_traceSegment_024_3408_0017, g32p_row03_traceSegment_024_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3375 33 34, g32p_row03_traceSegment_024_3375_0033, g32p_row03_traceSegment_024_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3442 8 9, g32p_row03_traceSegment_024_3442_0008, g32p_row03_traceSegment_024_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3459 8 9, g32p_row03_traceSegment_024_3459_0008, g32p_row03_traceSegment_024_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3442 17 17, g32p_row03_traceSegment_024_3442_0017, g32p_row03_traceSegment_024_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3476 8 9, g32p_row03_traceSegment_024_3476_0008, g32p_row03_traceSegment_024_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3493 8 9, g32p_row03_traceSegment_024_3493_0008, g32p_row03_traceSegment_024_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3476 17 17, g32p_row03_traceSegment_024_3476_0017, g32p_row03_traceSegment_024_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 3442 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3442 34 34, g32p_row03_traceSegment_024_3442_0034, g32p_row03_traceSegment_024_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 3375 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3375 67 68, g32p_row03_traceSegment_024_3375_0067, g32p_row03_traceSegment_024_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 3240 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3240 135 135, g32p_row03_traceSegment_024_3240_0135, g32p_row03_traceSegment_024_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3526 8 9, g32p_row03_traceSegment_024_3526_0008, g32p_row03_traceSegment_024_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3510 16 17, g32p_row03_traceSegment_024_3510_0016, g32p_row03_traceSegment_024_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3543 8 9, g32p_row03_traceSegment_024_3543_0008, g32p_row03_traceSegment_024_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3560 8 9, g32p_row03_traceSegment_024_3560_0008, g32p_row03_traceSegment_024_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3543 17 17, g32p_row03_traceSegment_024_3543_0017, g32p_row03_traceSegment_024_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3510 33 34, g32p_row03_traceSegment_024_3510_0033, g32p_row03_traceSegment_024_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3577 8 9, g32p_row03_traceSegment_024_3577_0008, g32p_row03_traceSegment_024_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3594 8 9, g32p_row03_traceSegment_024_3594_0008, g32p_row03_traceSegment_024_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3577 17 17, g32p_row03_traceSegment_024_3577_0017, g32p_row03_traceSegment_024_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3611 8 9, g32p_row03_traceSegment_024_3611_0008, g32p_row03_traceSegment_024_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3628 8 9, g32p_row03_traceSegment_024_3628_0008, g32p_row03_traceSegment_024_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3611 17 17, g32p_row03_traceSegment_024_3611_0017, g32p_row03_traceSegment_024_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 3577 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3577 34 34, g32p_row03_traceSegment_024_3577_0034, g32p_row03_traceSegment_024_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 3510 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3510 67 68, g32p_row03_traceSegment_024_3510_0067, g32p_row03_traceSegment_024_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3661 8 9, g32p_row03_traceSegment_024_3661_0008, g32p_row03_traceSegment_024_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3645 16 17, g32p_row03_traceSegment_024_3645_0016, g32p_row03_traceSegment_024_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3678 8 9, g32p_row03_traceSegment_024_3678_0008, g32p_row03_traceSegment_024_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3695 8 9, g32p_row03_traceSegment_024_3695_0008, g32p_row03_traceSegment_024_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3678 17 17, g32p_row03_traceSegment_024_3678_0017, g32p_row03_traceSegment_024_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3645 33 34, g32p_row03_traceSegment_024_3645_0033, g32p_row03_traceSegment_024_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3712 8 9, g32p_row03_traceSegment_024_3712_0008, g32p_row03_traceSegment_024_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3729 8 9, g32p_row03_traceSegment_024_3729_0008, g32p_row03_traceSegment_024_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3712 17 17, g32p_row03_traceSegment_024_3712_0017, g32p_row03_traceSegment_024_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3746 8 9, g32p_row03_traceSegment_024_3746_0008, g32p_row03_traceSegment_024_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3763 8 9, g32p_row03_traceSegment_024_3763_0008, g32p_row03_traceSegment_024_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3746 17 17, g32p_row03_traceSegment_024_3746_0017, g32p_row03_traceSegment_024_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 3712 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3712 34 34, g32p_row03_traceSegment_024_3712_0034, g32p_row03_traceSegment_024_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 3645 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3645 67 68, g32p_row03_traceSegment_024_3645_0067, g32p_row03_traceSegment_024_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 3510 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3510 135 135, g32p_row03_traceSegment_024_3510_0135, g32p_row03_traceSegment_024_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_024 3240 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3240 270 270, g32p_row03_traceSegment_024_3240_0270, g32p_row03_traceSegment_024_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3796 8 9, g32p_row03_traceSegment_024_3796_0008, g32p_row03_traceSegment_024_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3780 16 17, g32p_row03_traceSegment_024_3780_0016, g32p_row03_traceSegment_024_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3813 8 9, g32p_row03_traceSegment_024_3813_0008, g32p_row03_traceSegment_024_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3830 8 9, g32p_row03_traceSegment_024_3830_0008, g32p_row03_traceSegment_024_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3813 17 17, g32p_row03_traceSegment_024_3813_0017, g32p_row03_traceSegment_024_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3780 33 34, g32p_row03_traceSegment_024_3780_0033, g32p_row03_traceSegment_024_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3847 8 9, g32p_row03_traceSegment_024_3847_0008, g32p_row03_traceSegment_024_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3864 8 9, g32p_row03_traceSegment_024_3864_0008, g32p_row03_traceSegment_024_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3847 17 17, g32p_row03_traceSegment_024_3847_0017, g32p_row03_traceSegment_024_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3881 8 9, g32p_row03_traceSegment_024_3881_0008, g32p_row03_traceSegment_024_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3898 8 9, g32p_row03_traceSegment_024_3898_0008, g32p_row03_traceSegment_024_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3881 17 17, g32p_row03_traceSegment_024_3881_0017, g32p_row03_traceSegment_024_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3847 34 34, g32p_row03_traceSegment_024_3847_0034, g32p_row03_traceSegment_024_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 3780 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3780 67 68, g32p_row03_traceSegment_024_3780_0067, g32p_row03_traceSegment_024_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3931 8 9, g32p_row03_traceSegment_024_3931_0008, g32p_row03_traceSegment_024_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3915 16 17, g32p_row03_traceSegment_024_3915_0016, g32p_row03_traceSegment_024_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3948 8 9, g32p_row03_traceSegment_024_3948_0008, g32p_row03_traceSegment_024_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3965 8 9, g32p_row03_traceSegment_024_3965_0008, g32p_row03_traceSegment_024_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3948 17 17, g32p_row03_traceSegment_024_3948_0017, g32p_row03_traceSegment_024_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3915 33 34, g32p_row03_traceSegment_024_3915_0033, g32p_row03_traceSegment_024_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3982 8 9, g32p_row03_traceSegment_024_3982_0008, g32p_row03_traceSegment_024_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3999 8 9, g32p_row03_traceSegment_024_3999_0008, g32p_row03_traceSegment_024_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3982 17 17, g32p_row03_traceSegment_024_3982_0017, g32p_row03_traceSegment_024_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4016 8 9, g32p_row03_traceSegment_024_4016_0008, g32p_row03_traceSegment_024_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4033 8 9, g32p_row03_traceSegment_024_4033_0008, g32p_row03_traceSegment_024_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4016 17 17, g32p_row03_traceSegment_024_4016_0017, g32p_row03_traceSegment_024_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3982 34 34, g32p_row03_traceSegment_024_3982_0034, g32p_row03_traceSegment_024_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 3915 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3915 67 68, g32p_row03_traceSegment_024_3915_0067, g32p_row03_traceSegment_024_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 3780 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3780 135 135, g32p_row03_traceSegment_024_3780_0135, g32p_row03_traceSegment_024_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4066 8 9, g32p_row03_traceSegment_024_4066_0008, g32p_row03_traceSegment_024_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4050 16 17, g32p_row03_traceSegment_024_4050_0016, g32p_row03_traceSegment_024_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4083 8 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4091 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4083 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4083 8 9, g32p_row03_traceSegment_024_4083_0008, g32p_row03_traceSegment_024_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4100 8 9, g32p_row03_traceSegment_024_4100_0008, g32p_row03_traceSegment_024_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 4083 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4083 17 17, g32p_row03_traceSegment_024_4083_0017, g32p_row03_traceSegment_024_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 4050 67 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4050 33 34, g32p_row03_traceSegment_024_4050_0033, g32p_row03_traceSegment_024_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4117 8 9, g32p_row03_traceSegment_024_4117_0008, g32p_row03_traceSegment_024_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4134 8 9, g32p_row03_traceSegment_024_4134_0008, g32p_row03_traceSegment_024_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4117 17 17, g32p_row03_traceSegment_024_4117_0017, g32p_row03_traceSegment_024_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4151 8 9, g32p_row03_traceSegment_024_4151_0008, g32p_row03_traceSegment_024_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4168 8 9, g32p_row03_traceSegment_024_4168_0008, g32p_row03_traceSegment_024_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4151 17 17, g32p_row03_traceSegment_024_4151_0017, g32p_row03_traceSegment_024_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4117 34 34, g32p_row03_traceSegment_024_4117_0034, g32p_row03_traceSegment_024_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 4050 135 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4050 67 68, g32p_row03_traceSegment_024_4050_0067, g32p_row03_traceSegment_024_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_024 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4201 8 9, g32p_row03_traceSegment_024_4201_0008, g32p_row03_traceSegment_024_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_024 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4185 16 17, g32p_row03_traceSegment_024_4185_0016, g32p_row03_traceSegment_024_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4218 8 9, g32p_row03_traceSegment_024_4218_0008, g32p_row03_traceSegment_024_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4243 9 = [1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4235 17 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4235 8 9, g32p_row03_traceSegment_024_4235_0008, g32p_row03_traceSegment_024_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 4218 34 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4218 17 17, g32p_row03_traceSegment_024_4218_0017, g32p_row03_traceSegment_024_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_024 4185 67 = [1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4185 33 34, g32p_row03_traceSegment_024_4185_0033, g32p_row03_traceSegment_024_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4252 8 9, g32p_row03_traceSegment_024_4252_0008, g32p_row03_traceSegment_024_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4269 8 9, g32p_row03_traceSegment_024_4269_0008, g32p_row03_traceSegment_024_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4252 17 17, g32p_row03_traceSegment_024_4252_0017, g32p_row03_traceSegment_024_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4286 8 9, g32p_row03_traceSegment_024_4286_0008, g32p_row03_traceSegment_024_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_024 4303 8 = [2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_024 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_024_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_024 4303 17 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4303 8 9, g32p_row03_traceSegment_024_4303_0008, g32p_row03_traceSegment_024_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_024 4286 34 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4286 17 17, g32p_row03_traceSegment_024_4286_0017, g32p_row03_traceSegment_024_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_024 4252 68 = [2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4252 34 34, g32p_row03_traceSegment_024_4252_0034, g32p_row03_traceSegment_024_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_024 4185 135 = [3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4185 67 68, g32p_row03_traceSegment_024_4185_0067, g32p_row03_traceSegment_024_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_024_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_024 4050 270 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 4050 135 135, g32p_row03_traceSegment_024_4050_0135, g32p_row03_traceSegment_024_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_024 3780 540 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3780 270 270, g32p_row03_traceSegment_024_3780_0270, g32p_row03_traceSegment_024_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_024_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_024 3240 1080 = [5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 3240 540 540, g32p_row03_traceSegment_024_3240_0540, g32p_row03_traceSegment_024_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_024_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_024 2160 2160 = [23] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 2160 1080 1080, g32p_row03_traceSegment_024_2160_1080, g32p_row03_traceSegment_024_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_024_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_024 0 4320 = [40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_024 0 2160 2160, g32p_row03_traceSegment_024_0000_2160, g32p_row03_traceSegment_024_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 24 = [40] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_024_0000_4320

end HodgeLean.Foundations.Program

end
end
