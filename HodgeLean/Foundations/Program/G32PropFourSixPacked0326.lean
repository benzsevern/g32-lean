import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_056 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 56 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_056_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 16 8 9, g32p_row03_traceSegment_056_0016_0008, g32p_row03_traceSegment_056_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 0 16 17, g32p_row03_traceSegment_056_0000_0016, g32p_row03_traceSegment_056_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 33 8 9, g32p_row03_traceSegment_056_0033_0008, g32p_row03_traceSegment_056_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 50 8 9, g32p_row03_traceSegment_056_0050_0008, g32p_row03_traceSegment_056_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 33 17 17, g32p_row03_traceSegment_056_0033_0017, g32p_row03_traceSegment_056_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 0 33 34, g32p_row03_traceSegment_056_0000_0033, g32p_row03_traceSegment_056_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 67 8 9, g32p_row03_traceSegment_056_0067_0008, g32p_row03_traceSegment_056_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 84 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 84 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 84 8 9, g32p_row03_traceSegment_056_0084_0008, g32p_row03_traceSegment_056_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 67 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 67 17 17, g32p_row03_traceSegment_056_0067_0017, g32p_row03_traceSegment_056_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 101 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 109 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 101 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 101 8 9, g32p_row03_traceSegment_056_0101_0008, g32p_row03_traceSegment_056_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 118 8 9, g32p_row03_traceSegment_056_0118_0008, g32p_row03_traceSegment_056_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 101 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 101 17 17, g32p_row03_traceSegment_056_0101_0017, g32p_row03_traceSegment_056_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 67 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 67 34 34, g32p_row03_traceSegment_056_0067_0034, g32p_row03_traceSegment_056_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 0 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 0 67 68, g32p_row03_traceSegment_056_0000_0067, g32p_row03_traceSegment_056_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 151 8 9, g32p_row03_traceSegment_056_0151_0008, g32p_row03_traceSegment_056_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 135 16 17, g32p_row03_traceSegment_056_0135_0016, g32p_row03_traceSegment_056_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 168 8 9, g32p_row03_traceSegment_056_0168_0008, g32p_row03_traceSegment_056_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 185 8 9, g32p_row03_traceSegment_056_0185_0008, g32p_row03_traceSegment_056_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 168 17 17, g32p_row03_traceSegment_056_0168_0017, g32p_row03_traceSegment_056_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 135 33 34, g32p_row03_traceSegment_056_0135_0033, g32p_row03_traceSegment_056_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 202 8 9, g32p_row03_traceSegment_056_0202_0008, g32p_row03_traceSegment_056_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 219 8 9, g32p_row03_traceSegment_056_0219_0008, g32p_row03_traceSegment_056_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 202 17 17, g32p_row03_traceSegment_056_0202_0017, g32p_row03_traceSegment_056_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 236 8 9, g32p_row03_traceSegment_056_0236_0008, g32p_row03_traceSegment_056_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 253 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 253 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 253 8 9, g32p_row03_traceSegment_056_0253_0008, g32p_row03_traceSegment_056_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 236 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 236 17 17, g32p_row03_traceSegment_056_0236_0017, g32p_row03_traceSegment_056_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 202 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 202 34 34, g32p_row03_traceSegment_056_0202_0034, g32p_row03_traceSegment_056_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 135 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 135 67 68, g32p_row03_traceSegment_056_0135_0067, g32p_row03_traceSegment_056_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 0 270 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 0 135 135, g32p_row03_traceSegment_056_0000_0135, g32p_row03_traceSegment_056_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 270 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 286 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 286 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 286 8 9, g32p_row03_traceSegment_056_0286_0008, g32p_row03_traceSegment_056_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 270 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 270 16 17, g32p_row03_traceSegment_056_0270_0016, g32p_row03_traceSegment_056_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 303 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 303 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 303 8 9, g32p_row03_traceSegment_056_0303_0008, g32p_row03_traceSegment_056_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 328 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 320 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 320 8 9, g32p_row03_traceSegment_056_0320_0008, g32p_row03_traceSegment_056_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 303 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 303 17 17, g32p_row03_traceSegment_056_0303_0017, g32p_row03_traceSegment_056_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 270 67 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 270 33 34, g32p_row03_traceSegment_056_0270_0033, g32p_row03_traceSegment_056_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 337 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 337 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 337 8 9, g32p_row03_traceSegment_056_0337_0008, g32p_row03_traceSegment_056_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 354 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 354 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 354 8 9, g32p_row03_traceSegment_056_0354_0008, g32p_row03_traceSegment_056_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 337 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 337 17 17, g32p_row03_traceSegment_056_0337_0017, g32p_row03_traceSegment_056_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 371 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 371 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 371 8 9, g32p_row03_traceSegment_056_0371_0008, g32p_row03_traceSegment_056_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 388 8 9, g32p_row03_traceSegment_056_0388_0008, g32p_row03_traceSegment_056_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 371 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 371 17 17, g32p_row03_traceSegment_056_0371_0017, g32p_row03_traceSegment_056_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 337 68 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 337 34 34, g32p_row03_traceSegment_056_0337_0034, g32p_row03_traceSegment_056_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 270 135 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 270 67 68, g32p_row03_traceSegment_056_0270_0067, g32p_row03_traceSegment_056_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 421 8 9, g32p_row03_traceSegment_056_0421_0008, g32p_row03_traceSegment_056_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 405 16 17, g32p_row03_traceSegment_056_0405_0016, g32p_row03_traceSegment_056_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 438 8 9, g32p_row03_traceSegment_056_0438_0008, g32p_row03_traceSegment_056_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 455 8 9, g32p_row03_traceSegment_056_0455_0008, g32p_row03_traceSegment_056_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 438 17 17, g32p_row03_traceSegment_056_0438_0017, g32p_row03_traceSegment_056_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 405 33 34, g32p_row03_traceSegment_056_0405_0033, g32p_row03_traceSegment_056_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 472 8 9, g32p_row03_traceSegment_056_0472_0008, g32p_row03_traceSegment_056_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 489 8 9, g32p_row03_traceSegment_056_0489_0008, g32p_row03_traceSegment_056_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 472 17 17, g32p_row03_traceSegment_056_0472_0017, g32p_row03_traceSegment_056_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 506 8 9, g32p_row03_traceSegment_056_0506_0008, g32p_row03_traceSegment_056_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 523 8 9, g32p_row03_traceSegment_056_0523_0008, g32p_row03_traceSegment_056_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 506 17 17, g32p_row03_traceSegment_056_0506_0017, g32p_row03_traceSegment_056_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 472 34 34, g32p_row03_traceSegment_056_0472_0034, g32p_row03_traceSegment_056_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 405 67 68, g32p_row03_traceSegment_056_0405_0067, g32p_row03_traceSegment_056_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 270 270 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 270 135 135, g32p_row03_traceSegment_056_0270_0135, g32p_row03_traceSegment_056_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_056 0 540 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 0 270 270, g32p_row03_traceSegment_056_0000_0270, g32p_row03_traceSegment_056_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 556 8 9, g32p_row03_traceSegment_056_0556_0008, g32p_row03_traceSegment_056_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 540 16 17, g32p_row03_traceSegment_056_0540_0016, g32p_row03_traceSegment_056_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 573 8 9, g32p_row03_traceSegment_056_0573_0008, g32p_row03_traceSegment_056_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 590 8 9, g32p_row03_traceSegment_056_0590_0008, g32p_row03_traceSegment_056_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 573 17 17, g32p_row03_traceSegment_056_0573_0017, g32p_row03_traceSegment_056_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 540 33 34, g32p_row03_traceSegment_056_0540_0033, g32p_row03_traceSegment_056_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 607 8 9, g32p_row03_traceSegment_056_0607_0008, g32p_row03_traceSegment_056_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 624 8 9, g32p_row03_traceSegment_056_0624_0008, g32p_row03_traceSegment_056_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 607 17 17, g32p_row03_traceSegment_056_0607_0017, g32p_row03_traceSegment_056_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 641 8 9, g32p_row03_traceSegment_056_0641_0008, g32p_row03_traceSegment_056_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 658 8 9, g32p_row03_traceSegment_056_0658_0008, g32p_row03_traceSegment_056_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 641 17 17, g32p_row03_traceSegment_056_0641_0017, g32p_row03_traceSegment_056_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 607 34 34, g32p_row03_traceSegment_056_0607_0034, g32p_row03_traceSegment_056_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 540 67 68, g32p_row03_traceSegment_056_0540_0067, g32p_row03_traceSegment_056_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 691 8 9, g32p_row03_traceSegment_056_0691_0008, g32p_row03_traceSegment_056_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 675 16 17, g32p_row03_traceSegment_056_0675_0016, g32p_row03_traceSegment_056_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 708 8 9, g32p_row03_traceSegment_056_0708_0008, g32p_row03_traceSegment_056_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 725 8 9, g32p_row03_traceSegment_056_0725_0008, g32p_row03_traceSegment_056_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 708 17 17, g32p_row03_traceSegment_056_0708_0017, g32p_row03_traceSegment_056_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 675 33 34, g32p_row03_traceSegment_056_0675_0033, g32p_row03_traceSegment_056_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 742 8 9, g32p_row03_traceSegment_056_0742_0008, g32p_row03_traceSegment_056_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 759 8 9, g32p_row03_traceSegment_056_0759_0008, g32p_row03_traceSegment_056_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 742 17 17, g32p_row03_traceSegment_056_0742_0017, g32p_row03_traceSegment_056_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 784 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 776 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 776 8 9, g32p_row03_traceSegment_056_0776_0008, g32p_row03_traceSegment_056_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 793 8 9, g32p_row03_traceSegment_056_0793_0008, g32p_row03_traceSegment_056_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 776 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 776 17 17, g32p_row03_traceSegment_056_0776_0017, g32p_row03_traceSegment_056_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 742 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 742 34 34, g32p_row03_traceSegment_056_0742_0034, g32p_row03_traceSegment_056_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 675 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 675 67 68, g32p_row03_traceSegment_056_0675_0067, g32p_row03_traceSegment_056_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 540 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 540 135 135, g32p_row03_traceSegment_056_0540_0135, g32p_row03_traceSegment_056_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 826 8 9, g32p_row03_traceSegment_056_0826_0008, g32p_row03_traceSegment_056_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 810 16 17, g32p_row03_traceSegment_056_0810_0016, g32p_row03_traceSegment_056_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 843 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 843 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 843 8 9, g32p_row03_traceSegment_056_0843_0008, g32p_row03_traceSegment_056_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 860 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 860 8 9, g32p_row03_traceSegment_056_0860_0008, g32p_row03_traceSegment_056_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 843 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 843 17 17, g32p_row03_traceSegment_056_0843_0017, g32p_row03_traceSegment_056_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 810 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 810 33 34, g32p_row03_traceSegment_056_0810_0033, g32p_row03_traceSegment_056_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 877 8 9, g32p_row03_traceSegment_056_0877_0008, g32p_row03_traceSegment_056_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 894 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 894 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 894 8 9, g32p_row03_traceSegment_056_0894_0008, g32p_row03_traceSegment_056_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 877 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 877 17 17, g32p_row03_traceSegment_056_0877_0017, g32p_row03_traceSegment_056_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 919 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 911 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 911 8 9, g32p_row03_traceSegment_056_0911_0008, g32p_row03_traceSegment_056_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 928 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 928 8 9, g32p_row03_traceSegment_056_0928_0008, g32p_row03_traceSegment_056_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 911 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 911 17 17, g32p_row03_traceSegment_056_0911_0017, g32p_row03_traceSegment_056_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 877 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 877 34 34, g32p_row03_traceSegment_056_0877_0034, g32p_row03_traceSegment_056_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 810 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 810 67 68, g32p_row03_traceSegment_056_0810_0067, g32p_row03_traceSegment_056_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 945 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 969 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 961 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 961 8 9, g32p_row03_traceSegment_056_0961_0008, g32p_row03_traceSegment_056_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 945 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 945 16 17, g32p_row03_traceSegment_056_0945_0016, g32p_row03_traceSegment_056_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 978 8 9, g32p_row03_traceSegment_056_0978_0008, g32p_row03_traceSegment_056_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 995 8 9, g32p_row03_traceSegment_056_0995_0008, g32p_row03_traceSegment_056_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 978 17 17, g32p_row03_traceSegment_056_0978_0017, g32p_row03_traceSegment_056_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 945 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 945 33 34, g32p_row03_traceSegment_056_0945_0033, g32p_row03_traceSegment_056_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1012 8 9, g32p_row03_traceSegment_056_1012_0008, g32p_row03_traceSegment_056_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1029 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1037 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1029 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1029 8 9, g32p_row03_traceSegment_056_1029_0008, g32p_row03_traceSegment_056_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1012 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1012 17 17, g32p_row03_traceSegment_056_1012_0017, g32p_row03_traceSegment_056_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1046 8 9, g32p_row03_traceSegment_056_1046_0008, g32p_row03_traceSegment_056_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1063 8 9, g32p_row03_traceSegment_056_1063_0008, g32p_row03_traceSegment_056_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1046 17 17, g32p_row03_traceSegment_056_1046_0017, g32p_row03_traceSegment_056_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 1012 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1012 34 34, g32p_row03_traceSegment_056_1012_0034, g32p_row03_traceSegment_056_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 945 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 945 67 68, g32p_row03_traceSegment_056_0945_0067, g32p_row03_traceSegment_056_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 810 270 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 810 135 135, g32p_row03_traceSegment_056_0810_0135, g32p_row03_traceSegment_056_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_056 540 540 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 540 270 270, g32p_row03_traceSegment_056_0540_0270, g32p_row03_traceSegment_056_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_056 0 1080 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 0 540 540, g32p_row03_traceSegment_056_0000_0540, g32p_row03_traceSegment_056_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1096 8 9, g32p_row03_traceSegment_056_1096_0008, g32p_row03_traceSegment_056_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1080 16 17, g32p_row03_traceSegment_056_1080_0016, g32p_row03_traceSegment_056_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1113 8 9, g32p_row03_traceSegment_056_1113_0008, g32p_row03_traceSegment_056_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1130 8 9, g32p_row03_traceSegment_056_1130_0008, g32p_row03_traceSegment_056_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1113 17 17, g32p_row03_traceSegment_056_1113_0017, g32p_row03_traceSegment_056_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1080 33 34, g32p_row03_traceSegment_056_1080_0033, g32p_row03_traceSegment_056_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1147 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1147 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1147 8 9, g32p_row03_traceSegment_056_1147_0008, g32p_row03_traceSegment_056_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1164 8 9, g32p_row03_traceSegment_056_1164_0008, g32p_row03_traceSegment_056_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1147 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1147 17 17, g32p_row03_traceSegment_056_1147_0017, g32p_row03_traceSegment_056_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1181 8 9, g32p_row03_traceSegment_056_1181_0008, g32p_row03_traceSegment_056_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1198 8 9, g32p_row03_traceSegment_056_1198_0008, g32p_row03_traceSegment_056_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1181 17 17, g32p_row03_traceSegment_056_1181_0017, g32p_row03_traceSegment_056_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 1147 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1147 34 34, g32p_row03_traceSegment_056_1147_0034, g32p_row03_traceSegment_056_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 1080 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1080 67 68, g32p_row03_traceSegment_056_1080_0067, g32p_row03_traceSegment_056_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1231 8 9, g32p_row03_traceSegment_056_1231_0008, g32p_row03_traceSegment_056_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1215 16 17, g32p_row03_traceSegment_056_1215_0016, g32p_row03_traceSegment_056_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1248 8 9, g32p_row03_traceSegment_056_1248_0008, g32p_row03_traceSegment_056_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1265 8 9, g32p_row03_traceSegment_056_1265_0008, g32p_row03_traceSegment_056_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1248 17 17, g32p_row03_traceSegment_056_1248_0017, g32p_row03_traceSegment_056_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1215 33 34, g32p_row03_traceSegment_056_1215_0033, g32p_row03_traceSegment_056_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1282 8 9, g32p_row03_traceSegment_056_1282_0008, g32p_row03_traceSegment_056_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1299 8 9, g32p_row03_traceSegment_056_1299_0008, g32p_row03_traceSegment_056_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1282 17 17, g32p_row03_traceSegment_056_1282_0017, g32p_row03_traceSegment_056_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1316 8 9, g32p_row03_traceSegment_056_1316_0008, g32p_row03_traceSegment_056_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1333 8 9, g32p_row03_traceSegment_056_1333_0008, g32p_row03_traceSegment_056_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1316 17 17, g32p_row03_traceSegment_056_1316_0017, g32p_row03_traceSegment_056_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1282 34 34, g32p_row03_traceSegment_056_1282_0034, g32p_row03_traceSegment_056_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1215 67 68, g32p_row03_traceSegment_056_1215_0067, g32p_row03_traceSegment_056_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 1080 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1080 135 135, g32p_row03_traceSegment_056_1080_0135, g32p_row03_traceSegment_056_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1366 8 9, g32p_row03_traceSegment_056_1366_0008, g32p_row03_traceSegment_056_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1350 16 17, g32p_row03_traceSegment_056_1350_0016, g32p_row03_traceSegment_056_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1383 8 9, g32p_row03_traceSegment_056_1383_0008, g32p_row03_traceSegment_056_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1400 8 9, g32p_row03_traceSegment_056_1400_0008, g32p_row03_traceSegment_056_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1383 17 17, g32p_row03_traceSegment_056_1383_0017, g32p_row03_traceSegment_056_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1350 33 34, g32p_row03_traceSegment_056_1350_0033, g32p_row03_traceSegment_056_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1425 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1417 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1417 8 9, g32p_row03_traceSegment_056_1417_0008, g32p_row03_traceSegment_056_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1434 8 9, g32p_row03_traceSegment_056_1434_0008, g32p_row03_traceSegment_056_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1417 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1417 17 17, g32p_row03_traceSegment_056_1417_0017, g32p_row03_traceSegment_056_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1451 8 9, g32p_row03_traceSegment_056_1451_0008, g32p_row03_traceSegment_056_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1468 8 9, g32p_row03_traceSegment_056_1468_0008, g32p_row03_traceSegment_056_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1451 17 17, g32p_row03_traceSegment_056_1451_0017, g32p_row03_traceSegment_056_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 1417 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1417 34 34, g32p_row03_traceSegment_056_1417_0034, g32p_row03_traceSegment_056_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 1350 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1350 67 68, g32p_row03_traceSegment_056_1350_0067, g32p_row03_traceSegment_056_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1501 8 9, g32p_row03_traceSegment_056_1501_0008, g32p_row03_traceSegment_056_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1485 16 17, g32p_row03_traceSegment_056_1485_0016, g32p_row03_traceSegment_056_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1518 8 9, g32p_row03_traceSegment_056_1518_0008, g32p_row03_traceSegment_056_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1535 8 9, g32p_row03_traceSegment_056_1535_0008, g32p_row03_traceSegment_056_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1518 17 17, g32p_row03_traceSegment_056_1518_0017, g32p_row03_traceSegment_056_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1485 33 34, g32p_row03_traceSegment_056_1485_0033, g32p_row03_traceSegment_056_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1552 8 9, g32p_row03_traceSegment_056_1552_0008, g32p_row03_traceSegment_056_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1569 8 9, g32p_row03_traceSegment_056_1569_0008, g32p_row03_traceSegment_056_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1552 17 17, g32p_row03_traceSegment_056_1552_0017, g32p_row03_traceSegment_056_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1594 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1586 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1586 8 9, g32p_row03_traceSegment_056_1586_0008, g32p_row03_traceSegment_056_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1603 8 9, g32p_row03_traceSegment_056_1603_0008, g32p_row03_traceSegment_056_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1586 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1586 17 17, g32p_row03_traceSegment_056_1586_0017, g32p_row03_traceSegment_056_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 1552 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1552 34 34, g32p_row03_traceSegment_056_1552_0034, g32p_row03_traceSegment_056_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 1485 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1485 67 68, g32p_row03_traceSegment_056_1485_0067, g32p_row03_traceSegment_056_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 1350 270 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1350 135 135, g32p_row03_traceSegment_056_1350_0135, g32p_row03_traceSegment_056_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_056 1080 540 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1080 270 270, g32p_row03_traceSegment_056_1080_0270, g32p_row03_traceSegment_056_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1636 8 9, g32p_row03_traceSegment_056_1636_0008, g32p_row03_traceSegment_056_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1620 16 17, g32p_row03_traceSegment_056_1620_0016, g32p_row03_traceSegment_056_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1653 8 9, g32p_row03_traceSegment_056_1653_0008, g32p_row03_traceSegment_056_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1670 8 9, g32p_row03_traceSegment_056_1670_0008, g32p_row03_traceSegment_056_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1653 17 17, g32p_row03_traceSegment_056_1653_0017, g32p_row03_traceSegment_056_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1620 33 34, g32p_row03_traceSegment_056_1620_0033, g32p_row03_traceSegment_056_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1687 8 9, g32p_row03_traceSegment_056_1687_0008, g32p_row03_traceSegment_056_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1704 8 9, g32p_row03_traceSegment_056_1704_0008, g32p_row03_traceSegment_056_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1687 17 17, g32p_row03_traceSegment_056_1687_0017, g32p_row03_traceSegment_056_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1729 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1721 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1721 8 9, g32p_row03_traceSegment_056_1721_0008, g32p_row03_traceSegment_056_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1738 8 9, g32p_row03_traceSegment_056_1738_0008, g32p_row03_traceSegment_056_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1721 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1721 17 17, g32p_row03_traceSegment_056_1721_0017, g32p_row03_traceSegment_056_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 1687 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1687 34 34, g32p_row03_traceSegment_056_1687_0034, g32p_row03_traceSegment_056_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 1620 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1620 67 68, g32p_row03_traceSegment_056_1620_0067, g32p_row03_traceSegment_056_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1771 8 9, g32p_row03_traceSegment_056_1771_0008, g32p_row03_traceSegment_056_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1755 16 17, g32p_row03_traceSegment_056_1755_0016, g32p_row03_traceSegment_056_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1788 8 9, g32p_row03_traceSegment_056_1788_0008, g32p_row03_traceSegment_056_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1805 8 9, g32p_row03_traceSegment_056_1805_0008, g32p_row03_traceSegment_056_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1788 17 17, g32p_row03_traceSegment_056_1788_0017, g32p_row03_traceSegment_056_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1755 33 34, g32p_row03_traceSegment_056_1755_0033, g32p_row03_traceSegment_056_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1822 8 9, g32p_row03_traceSegment_056_1822_0008, g32p_row03_traceSegment_056_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1847 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1839 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1839 8 9, g32p_row03_traceSegment_056_1839_0008, g32p_row03_traceSegment_056_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1822 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1822 17 17, g32p_row03_traceSegment_056_1822_0017, g32p_row03_traceSegment_056_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1856 8 9, g32p_row03_traceSegment_056_1856_0008, g32p_row03_traceSegment_056_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1881 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1873 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1873 8 9, g32p_row03_traceSegment_056_1873_0008, g32p_row03_traceSegment_056_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1856 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1856 17 17, g32p_row03_traceSegment_056_1856_0017, g32p_row03_traceSegment_056_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 1822 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1822 34 34, g32p_row03_traceSegment_056_1822_0034, g32p_row03_traceSegment_056_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 1755 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1755 67 68, g32p_row03_traceSegment_056_1755_0067, g32p_row03_traceSegment_056_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 1620 270 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1620 135 135, g32p_row03_traceSegment_056_1620_0135, g32p_row03_traceSegment_056_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1906 8 9, g32p_row03_traceSegment_056_1906_0008, g32p_row03_traceSegment_056_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1890 16 17, g32p_row03_traceSegment_056_1890_0016, g32p_row03_traceSegment_056_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1923 8 9, g32p_row03_traceSegment_056_1923_0008, g32p_row03_traceSegment_056_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1940 8 9, g32p_row03_traceSegment_056_1940_0008, g32p_row03_traceSegment_056_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1923 17 17, g32p_row03_traceSegment_056_1923_0017, g32p_row03_traceSegment_056_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1890 33 34, g32p_row03_traceSegment_056_1890_0033, g32p_row03_traceSegment_056_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1965 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1957 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1957 8 9, g32p_row03_traceSegment_056_1957_0008, g32p_row03_traceSegment_056_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1974 8 9, g32p_row03_traceSegment_056_1974_0008, g32p_row03_traceSegment_056_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1957 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1957 17 17, g32p_row03_traceSegment_056_1957_0017, g32p_row03_traceSegment_056_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1991 8 9, g32p_row03_traceSegment_056_1991_0008, g32p_row03_traceSegment_056_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2016 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2008 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2008 8 9, g32p_row03_traceSegment_056_2008_0008, g32p_row03_traceSegment_056_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 1991 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1991 17 17, g32p_row03_traceSegment_056_1991_0017, g32p_row03_traceSegment_056_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 1957 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1957 34 34, g32p_row03_traceSegment_056_1957_0034, g32p_row03_traceSegment_056_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 1890 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1890 67 68, g32p_row03_traceSegment_056_1890_0067, g32p_row03_traceSegment_056_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 2025 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2049 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2041 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2041 8 9, g32p_row03_traceSegment_056_2041_0008, g32p_row03_traceSegment_056_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 2025 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2025 16 17, g32p_row03_traceSegment_056_2025_0016, g32p_row03_traceSegment_056_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2058 8 9, g32p_row03_traceSegment_056_2058_0008, g32p_row03_traceSegment_056_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2075 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2075 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2075 8 9, g32p_row03_traceSegment_056_2075_0008, g32p_row03_traceSegment_056_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2058 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2058 17 17, g32p_row03_traceSegment_056_2058_0017, g32p_row03_traceSegment_056_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 2025 67 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2025 33 34, g32p_row03_traceSegment_056_2025_0033, g32p_row03_traceSegment_056_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2092 8 9, g32p_row03_traceSegment_056_2092_0008, g32p_row03_traceSegment_056_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2109 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2109 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2109 8 9, g32p_row03_traceSegment_056_2109_0008, g32p_row03_traceSegment_056_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2092 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2092 17 17, g32p_row03_traceSegment_056_2092_0017, g32p_row03_traceSegment_056_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2126 8 9, g32p_row03_traceSegment_056_2126_0008, g32p_row03_traceSegment_056_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2143 8 9, g32p_row03_traceSegment_056_2143_0008, g32p_row03_traceSegment_056_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2126 17 17, g32p_row03_traceSegment_056_2126_0017, g32p_row03_traceSegment_056_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 2092 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2092 34 34, g32p_row03_traceSegment_056_2092_0034, g32p_row03_traceSegment_056_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 2025 135 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2025 67 68, g32p_row03_traceSegment_056_2025_0067, g32p_row03_traceSegment_056_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 1890 270 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1890 135 135, g32p_row03_traceSegment_056_1890_0135, g32p_row03_traceSegment_056_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_056 1620 540 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1620 270 270, g32p_row03_traceSegment_056_1620_0270, g32p_row03_traceSegment_056_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_056_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_056 1080 1080 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 1080 540 540, g32p_row03_traceSegment_056_1080_0540, g32p_row03_traceSegment_056_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_056 0 2160 = [0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 0 1080 1080, g32p_row03_traceSegment_056_0000_1080, g32p_row03_traceSegment_056_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2176 8 9, g32p_row03_traceSegment_056_2176_0008, g32p_row03_traceSegment_056_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2160 16 17, g32p_row03_traceSegment_056_2160_0016, g32p_row03_traceSegment_056_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2201 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2193 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2193 8 9, g32p_row03_traceSegment_056_2193_0008, g32p_row03_traceSegment_056_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2210 8 9, g32p_row03_traceSegment_056_2210_0008, g32p_row03_traceSegment_056_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2193 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2193 17 17, g32p_row03_traceSegment_056_2193_0017, g32p_row03_traceSegment_056_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 2160 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2160 33 34, g32p_row03_traceSegment_056_2160_0033, g32p_row03_traceSegment_056_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2227 8 9, g32p_row03_traceSegment_056_2227_0008, g32p_row03_traceSegment_056_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2244 8 9, g32p_row03_traceSegment_056_2244_0008, g32p_row03_traceSegment_056_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2227 17 17, g32p_row03_traceSegment_056_2227_0017, g32p_row03_traceSegment_056_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2261 8 9, g32p_row03_traceSegment_056_2261_0008, g32p_row03_traceSegment_056_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2278 8 9, g32p_row03_traceSegment_056_2278_0008, g32p_row03_traceSegment_056_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2261 17 17, g32p_row03_traceSegment_056_2261_0017, g32p_row03_traceSegment_056_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2227 34 34, g32p_row03_traceSegment_056_2227_0034, g32p_row03_traceSegment_056_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 2160 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2160 67 68, g32p_row03_traceSegment_056_2160_0067, g32p_row03_traceSegment_056_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2311 8 9, g32p_row03_traceSegment_056_2311_0008, g32p_row03_traceSegment_056_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2295 16 17, g32p_row03_traceSegment_056_2295_0016, g32p_row03_traceSegment_056_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2328 8 9, g32p_row03_traceSegment_056_2328_0008, g32p_row03_traceSegment_056_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2345 8 9, g32p_row03_traceSegment_056_2345_0008, g32p_row03_traceSegment_056_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2328 17 17, g32p_row03_traceSegment_056_2328_0017, g32p_row03_traceSegment_056_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 2295 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2295 33 34, g32p_row03_traceSegment_056_2295_0033, g32p_row03_traceSegment_056_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2362 8 9, g32p_row03_traceSegment_056_2362_0008, g32p_row03_traceSegment_056_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2379 8 9, g32p_row03_traceSegment_056_2379_0008, g32p_row03_traceSegment_056_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2362 17 17, g32p_row03_traceSegment_056_2362_0017, g32p_row03_traceSegment_056_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2396 8 9, g32p_row03_traceSegment_056_2396_0008, g32p_row03_traceSegment_056_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2413 8 9, g32p_row03_traceSegment_056_2413_0008, g32p_row03_traceSegment_056_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2396 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2396 17 17, g32p_row03_traceSegment_056_2396_0017, g32p_row03_traceSegment_056_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 2362 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2362 34 34, g32p_row03_traceSegment_056_2362_0034, g32p_row03_traceSegment_056_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 2295 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2295 67 68, g32p_row03_traceSegment_056_2295_0067, g32p_row03_traceSegment_056_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 2160 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2160 135 135, g32p_row03_traceSegment_056_2160_0135, g32p_row03_traceSegment_056_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2446 8 9, g32p_row03_traceSegment_056_2446_0008, g32p_row03_traceSegment_056_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2430 16 17, g32p_row03_traceSegment_056_2430_0016, g32p_row03_traceSegment_056_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2463 8 9, g32p_row03_traceSegment_056_2463_0008, g32p_row03_traceSegment_056_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2480 8 9, g32p_row03_traceSegment_056_2480_0008, g32p_row03_traceSegment_056_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2463 17 17, g32p_row03_traceSegment_056_2463_0017, g32p_row03_traceSegment_056_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 2430 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2430 33 34, g32p_row03_traceSegment_056_2430_0033, g32p_row03_traceSegment_056_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2497 8 9, g32p_row03_traceSegment_056_2497_0008, g32p_row03_traceSegment_056_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2514 8 9, g32p_row03_traceSegment_056_2514_0008, g32p_row03_traceSegment_056_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2497 17 17, g32p_row03_traceSegment_056_2497_0017, g32p_row03_traceSegment_056_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2531 8 9, g32p_row03_traceSegment_056_2531_0008, g32p_row03_traceSegment_056_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2548 8 9, g32p_row03_traceSegment_056_2548_0008, g32p_row03_traceSegment_056_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2531 17 17, g32p_row03_traceSegment_056_2531_0017, g32p_row03_traceSegment_056_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2497 34 34, g32p_row03_traceSegment_056_2497_0034, g32p_row03_traceSegment_056_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 2430 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2430 67 68, g32p_row03_traceSegment_056_2430_0067, g32p_row03_traceSegment_056_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2581 8 9, g32p_row03_traceSegment_056_2581_0008, g32p_row03_traceSegment_056_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2565 16 17, g32p_row03_traceSegment_056_2565_0016, g32p_row03_traceSegment_056_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2598 8 9, g32p_row03_traceSegment_056_2598_0008, g32p_row03_traceSegment_056_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2615 8 9, g32p_row03_traceSegment_056_2615_0008, g32p_row03_traceSegment_056_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2598 17 17, g32p_row03_traceSegment_056_2598_0017, g32p_row03_traceSegment_056_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 2565 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2565 33 34, g32p_row03_traceSegment_056_2565_0033, g32p_row03_traceSegment_056_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2632 8 9, g32p_row03_traceSegment_056_2632_0008, g32p_row03_traceSegment_056_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2649 8 9, g32p_row03_traceSegment_056_2649_0008, g32p_row03_traceSegment_056_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2632 17 17, g32p_row03_traceSegment_056_2632_0017, g32p_row03_traceSegment_056_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2666 8 9, g32p_row03_traceSegment_056_2666_0008, g32p_row03_traceSegment_056_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2683 8 9, g32p_row03_traceSegment_056_2683_0008, g32p_row03_traceSegment_056_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2666 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2666 17 17, g32p_row03_traceSegment_056_2666_0017, g32p_row03_traceSegment_056_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 2632 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2632 34 34, g32p_row03_traceSegment_056_2632_0034, g32p_row03_traceSegment_056_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 2565 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2565 67 68, g32p_row03_traceSegment_056_2565_0067, g32p_row03_traceSegment_056_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 2430 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2430 135 135, g32p_row03_traceSegment_056_2430_0135, g32p_row03_traceSegment_056_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_056 2160 540 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2160 270 270, g32p_row03_traceSegment_056_2160_0270, g32p_row03_traceSegment_056_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 2700 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2716 8 9, g32p_row03_traceSegment_056_2716_0008, g32p_row03_traceSegment_056_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 2700 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2700 16 17, g32p_row03_traceSegment_056_2700_0016, g32p_row03_traceSegment_056_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2733 8 9, g32p_row03_traceSegment_056_2733_0008, g32p_row03_traceSegment_056_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2750 8 9, g32p_row03_traceSegment_056_2750_0008, g32p_row03_traceSegment_056_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2733 17 17, g32p_row03_traceSegment_056_2733_0017, g32p_row03_traceSegment_056_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 2700 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2700 33 34, g32p_row03_traceSegment_056_2700_0033, g32p_row03_traceSegment_056_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2767 8 9, g32p_row03_traceSegment_056_2767_0008, g32p_row03_traceSegment_056_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2784 8 9, g32p_row03_traceSegment_056_2784_0008, g32p_row03_traceSegment_056_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2767 17 17, g32p_row03_traceSegment_056_2767_0017, g32p_row03_traceSegment_056_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2801 8 9, g32p_row03_traceSegment_056_2801_0008, g32p_row03_traceSegment_056_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2818 8 9, g32p_row03_traceSegment_056_2818_0008, g32p_row03_traceSegment_056_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2801 17 17, g32p_row03_traceSegment_056_2801_0017, g32p_row03_traceSegment_056_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2767 34 34, g32p_row03_traceSegment_056_2767_0034, g32p_row03_traceSegment_056_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 2700 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2700 67 68, g32p_row03_traceSegment_056_2700_0067, g32p_row03_traceSegment_056_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2851 8 9, g32p_row03_traceSegment_056_2851_0008, g32p_row03_traceSegment_056_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2835 16 17, g32p_row03_traceSegment_056_2835_0016, g32p_row03_traceSegment_056_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2868 8 9, g32p_row03_traceSegment_056_2868_0008, g32p_row03_traceSegment_056_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2885 8 9, g32p_row03_traceSegment_056_2885_0008, g32p_row03_traceSegment_056_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2868 17 17, g32p_row03_traceSegment_056_2868_0017, g32p_row03_traceSegment_056_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2835 33 34, g32p_row03_traceSegment_056_2835_0033, g32p_row03_traceSegment_056_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2902 8 9, g32p_row03_traceSegment_056_2902_0008, g32p_row03_traceSegment_056_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2919 8 9, g32p_row03_traceSegment_056_2919_0008, g32p_row03_traceSegment_056_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2902 17 17, g32p_row03_traceSegment_056_2902_0017, g32p_row03_traceSegment_056_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2936 8 9, g32p_row03_traceSegment_056_2936_0008, g32p_row03_traceSegment_056_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2953 8 9, g32p_row03_traceSegment_056_2953_0008, g32p_row03_traceSegment_056_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2936 17 17, g32p_row03_traceSegment_056_2936_0017, g32p_row03_traceSegment_056_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2902 34 34, g32p_row03_traceSegment_056_2902_0034, g32p_row03_traceSegment_056_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2835 67 68, g32p_row03_traceSegment_056_2835_0067, g32p_row03_traceSegment_056_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 2700 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2700 135 135, g32p_row03_traceSegment_056_2700_0135, g32p_row03_traceSegment_056_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2986 8 9, g32p_row03_traceSegment_056_2986_0008, g32p_row03_traceSegment_056_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2970 16 17, g32p_row03_traceSegment_056_2970_0016, g32p_row03_traceSegment_056_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3003 8 9, g32p_row03_traceSegment_056_3003_0008, g32p_row03_traceSegment_056_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3020 8 9, g32p_row03_traceSegment_056_3020_0008, g32p_row03_traceSegment_056_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3003 17 17, g32p_row03_traceSegment_056_3003_0017, g32p_row03_traceSegment_056_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2970 33 34, g32p_row03_traceSegment_056_2970_0033, g32p_row03_traceSegment_056_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3037 8 9, g32p_row03_traceSegment_056_3037_0008, g32p_row03_traceSegment_056_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3054 8 9, g32p_row03_traceSegment_056_3054_0008, g32p_row03_traceSegment_056_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3037 17 17, g32p_row03_traceSegment_056_3037_0017, g32p_row03_traceSegment_056_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3071 8 9, g32p_row03_traceSegment_056_3071_0008, g32p_row03_traceSegment_056_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3088 8 9, g32p_row03_traceSegment_056_3088_0008, g32p_row03_traceSegment_056_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3071 17 17, g32p_row03_traceSegment_056_3071_0017, g32p_row03_traceSegment_056_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3037 34 34, g32p_row03_traceSegment_056_3037_0034, g32p_row03_traceSegment_056_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2970 67 68, g32p_row03_traceSegment_056_2970_0067, g32p_row03_traceSegment_056_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3121 8 9, g32p_row03_traceSegment_056_3121_0008, g32p_row03_traceSegment_056_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3105 16 17, g32p_row03_traceSegment_056_3105_0016, g32p_row03_traceSegment_056_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3146 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3138 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3138 8 9, g32p_row03_traceSegment_056_3138_0008, g32p_row03_traceSegment_056_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3155 8 9, g32p_row03_traceSegment_056_3155_0008, g32p_row03_traceSegment_056_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3138 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3138 17 17, g32p_row03_traceSegment_056_3138_0017, g32p_row03_traceSegment_056_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 3105 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3105 33 34, g32p_row03_traceSegment_056_3105_0033, g32p_row03_traceSegment_056_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3172 8 9, g32p_row03_traceSegment_056_3172_0008, g32p_row03_traceSegment_056_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3189 8 9, g32p_row03_traceSegment_056_3189_0008, g32p_row03_traceSegment_056_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3172 17 17, g32p_row03_traceSegment_056_3172_0017, g32p_row03_traceSegment_056_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3206 8 9, g32p_row03_traceSegment_056_3206_0008, g32p_row03_traceSegment_056_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3223 8 9, g32p_row03_traceSegment_056_3223_0008, g32p_row03_traceSegment_056_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3206 17 17, g32p_row03_traceSegment_056_3206_0017, g32p_row03_traceSegment_056_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3172 34 34, g32p_row03_traceSegment_056_3172_0034, g32p_row03_traceSegment_056_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 3105 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3105 67 68, g32p_row03_traceSegment_056_3105_0067, g32p_row03_traceSegment_056_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 2970 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2970 135 135, g32p_row03_traceSegment_056_2970_0135, g32p_row03_traceSegment_056_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_056 2700 540 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2700 270 270, g32p_row03_traceSegment_056_2700_0270, g32p_row03_traceSegment_056_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_056 2160 1080 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2160 540 540, g32p_row03_traceSegment_056_2160_0540, g32p_row03_traceSegment_056_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3256 8 9, g32p_row03_traceSegment_056_3256_0008, g32p_row03_traceSegment_056_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3240 16 17, g32p_row03_traceSegment_056_3240_0016, g32p_row03_traceSegment_056_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3273 8 9, g32p_row03_traceSegment_056_3273_0008, g32p_row03_traceSegment_056_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3290 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3290 8 9, g32p_row03_traceSegment_056_3290_0008, g32p_row03_traceSegment_056_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3273 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3273 17 17, g32p_row03_traceSegment_056_3273_0017, g32p_row03_traceSegment_056_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 3240 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3240 33 34, g32p_row03_traceSegment_056_3240_0033, g32p_row03_traceSegment_056_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3307 8 9, g32p_row03_traceSegment_056_3307_0008, g32p_row03_traceSegment_056_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3324 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3324 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3324 8 9, g32p_row03_traceSegment_056_3324_0008, g32p_row03_traceSegment_056_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3307 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3307 17 17, g32p_row03_traceSegment_056_3307_0017, g32p_row03_traceSegment_056_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3341 8 9, g32p_row03_traceSegment_056_3341_0008, g32p_row03_traceSegment_056_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3358 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3358 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3358 8 9, g32p_row03_traceSegment_056_3358_0008, g32p_row03_traceSegment_056_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3341 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3341 17 17, g32p_row03_traceSegment_056_3341_0017, g32p_row03_traceSegment_056_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 3307 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3307 34 34, g32p_row03_traceSegment_056_3307_0034, g32p_row03_traceSegment_056_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 3240 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3240 67 68, g32p_row03_traceSegment_056_3240_0067, g32p_row03_traceSegment_056_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3399 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3391 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3391 8 9, g32p_row03_traceSegment_056_3391_0008, g32p_row03_traceSegment_056_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 3375 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3375 16 17, g32p_row03_traceSegment_056_3375_0016, g32p_row03_traceSegment_056_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3408 8 9, g32p_row03_traceSegment_056_3408_0008, g32p_row03_traceSegment_056_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3425 8 9, g32p_row03_traceSegment_056_3425_0008, g32p_row03_traceSegment_056_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3408 17 17, g32p_row03_traceSegment_056_3408_0017, g32p_row03_traceSegment_056_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 3375 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3375 33 34, g32p_row03_traceSegment_056_3375_0033, g32p_row03_traceSegment_056_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3450 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3442 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3442 8 9, g32p_row03_traceSegment_056_3442_0008, g32p_row03_traceSegment_056_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3459 8 9, g32p_row03_traceSegment_056_3459_0008, g32p_row03_traceSegment_056_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3442 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3442 17 17, g32p_row03_traceSegment_056_3442_0017, g32p_row03_traceSegment_056_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3476 8 9, g32p_row03_traceSegment_056_3476_0008, g32p_row03_traceSegment_056_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3501 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3493 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3493 8 9, g32p_row03_traceSegment_056_3493_0008, g32p_row03_traceSegment_056_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3476 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3476 17 17, g32p_row03_traceSegment_056_3476_0017, g32p_row03_traceSegment_056_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 3442 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3442 34 34, g32p_row03_traceSegment_056_3442_0034, g32p_row03_traceSegment_056_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 3375 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3375 67 68, g32p_row03_traceSegment_056_3375_0067, g32p_row03_traceSegment_056_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 3240 270 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3240 135 135, g32p_row03_traceSegment_056_3240_0135, g32p_row03_traceSegment_056_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3526 8 9, g32p_row03_traceSegment_056_3526_0008, g32p_row03_traceSegment_056_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 3510 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3510 16 17, g32p_row03_traceSegment_056_3510_0016, g32p_row03_traceSegment_056_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3543 8 9, g32p_row03_traceSegment_056_3543_0008, g32p_row03_traceSegment_056_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3560 8 9, g32p_row03_traceSegment_056_3560_0008, g32p_row03_traceSegment_056_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3543 17 17, g32p_row03_traceSegment_056_3543_0017, g32p_row03_traceSegment_056_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 3510 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3510 33 34, g32p_row03_traceSegment_056_3510_0033, g32p_row03_traceSegment_056_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3585 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3577 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3577 8 9, g32p_row03_traceSegment_056_3577_0008, g32p_row03_traceSegment_056_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3594 8 9, g32p_row03_traceSegment_056_3594_0008, g32p_row03_traceSegment_056_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3577 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3577 17 17, g32p_row03_traceSegment_056_3577_0017, g32p_row03_traceSegment_056_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3611 8 9, g32p_row03_traceSegment_056_3611_0008, g32p_row03_traceSegment_056_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3628 8 9, g32p_row03_traceSegment_056_3628_0008, g32p_row03_traceSegment_056_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3611 17 17, g32p_row03_traceSegment_056_3611_0017, g32p_row03_traceSegment_056_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 3577 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3577 34 34, g32p_row03_traceSegment_056_3577_0034, g32p_row03_traceSegment_056_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 3510 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3510 67 68, g32p_row03_traceSegment_056_3510_0067, g32p_row03_traceSegment_056_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 3645 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3661 8 9, g32p_row03_traceSegment_056_3661_0008, g32p_row03_traceSegment_056_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 3645 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3645 16 17, g32p_row03_traceSegment_056_3645_0016, g32p_row03_traceSegment_056_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3678 8 9, g32p_row03_traceSegment_056_3678_0008, g32p_row03_traceSegment_056_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3695 8 9, g32p_row03_traceSegment_056_3695_0008, g32p_row03_traceSegment_056_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3678 17 17, g32p_row03_traceSegment_056_3678_0017, g32p_row03_traceSegment_056_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 3645 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3645 33 34, g32p_row03_traceSegment_056_3645_0033, g32p_row03_traceSegment_056_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3712 8 9, g32p_row03_traceSegment_056_3712_0008, g32p_row03_traceSegment_056_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3729 8 9, g32p_row03_traceSegment_056_3729_0008, g32p_row03_traceSegment_056_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3712 17 17, g32p_row03_traceSegment_056_3712_0017, g32p_row03_traceSegment_056_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3746 8 9, g32p_row03_traceSegment_056_3746_0008, g32p_row03_traceSegment_056_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3763 8 9, g32p_row03_traceSegment_056_3763_0008, g32p_row03_traceSegment_056_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3746 17 17, g32p_row03_traceSegment_056_3746_0017, g32p_row03_traceSegment_056_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 3712 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3712 34 34, g32p_row03_traceSegment_056_3712_0034, g32p_row03_traceSegment_056_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 3645 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3645 67 68, g32p_row03_traceSegment_056_3645_0067, g32p_row03_traceSegment_056_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 3510 270 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3510 135 135, g32p_row03_traceSegment_056_3510_0135, g32p_row03_traceSegment_056_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_056 3240 540 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3240 270 270, g32p_row03_traceSegment_056_3240_0270, g32p_row03_traceSegment_056_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3796 8 9, g32p_row03_traceSegment_056_3796_0008, g32p_row03_traceSegment_056_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3780 16 17, g32p_row03_traceSegment_056_3780_0016, g32p_row03_traceSegment_056_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3813 8 9, g32p_row03_traceSegment_056_3813_0008, g32p_row03_traceSegment_056_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3830 8 9, g32p_row03_traceSegment_056_3830_0008, g32p_row03_traceSegment_056_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3813 17 17, g32p_row03_traceSegment_056_3813_0017, g32p_row03_traceSegment_056_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3780 33 34, g32p_row03_traceSegment_056_3780_0033, g32p_row03_traceSegment_056_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3847 8 9, g32p_row03_traceSegment_056_3847_0008, g32p_row03_traceSegment_056_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3864 8 9, g32p_row03_traceSegment_056_3864_0008, g32p_row03_traceSegment_056_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3847 17 17, g32p_row03_traceSegment_056_3847_0017, g32p_row03_traceSegment_056_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3881 8 9, g32p_row03_traceSegment_056_3881_0008, g32p_row03_traceSegment_056_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3898 8 9, g32p_row03_traceSegment_056_3898_0008, g32p_row03_traceSegment_056_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3881 17 17, g32p_row03_traceSegment_056_3881_0017, g32p_row03_traceSegment_056_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3847 34 34, g32p_row03_traceSegment_056_3847_0034, g32p_row03_traceSegment_056_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 3780 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3780 67 68, g32p_row03_traceSegment_056_3780_0067, g32p_row03_traceSegment_056_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3931 8 9, g32p_row03_traceSegment_056_3931_0008, g32p_row03_traceSegment_056_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3915 16 17, g32p_row03_traceSegment_056_3915_0016, g32p_row03_traceSegment_056_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3948 8 9, g32p_row03_traceSegment_056_3948_0008, g32p_row03_traceSegment_056_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3965 8 9, g32p_row03_traceSegment_056_3965_0008, g32p_row03_traceSegment_056_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3948 17 17, g32p_row03_traceSegment_056_3948_0017, g32p_row03_traceSegment_056_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3915 33 34, g32p_row03_traceSegment_056_3915_0033, g32p_row03_traceSegment_056_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3982 8 9, g32p_row03_traceSegment_056_3982_0008, g32p_row03_traceSegment_056_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3999 8 9, g32p_row03_traceSegment_056_3999_0008, g32p_row03_traceSegment_056_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3982 17 17, g32p_row03_traceSegment_056_3982_0017, g32p_row03_traceSegment_056_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4016 8 9, g32p_row03_traceSegment_056_4016_0008, g32p_row03_traceSegment_056_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4033 8 9, g32p_row03_traceSegment_056_4033_0008, g32p_row03_traceSegment_056_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4016 17 17, g32p_row03_traceSegment_056_4016_0017, g32p_row03_traceSegment_056_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3982 34 34, g32p_row03_traceSegment_056_3982_0034, g32p_row03_traceSegment_056_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 3915 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3915 67 68, g32p_row03_traceSegment_056_3915_0067, g32p_row03_traceSegment_056_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 3780 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3780 135 135, g32p_row03_traceSegment_056_3780_0135, g32p_row03_traceSegment_056_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4066 8 9, g32p_row03_traceSegment_056_4066_0008, g32p_row03_traceSegment_056_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4050 16 17, g32p_row03_traceSegment_056_4050_0016, g32p_row03_traceSegment_056_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4083 8 9, g32p_row03_traceSegment_056_4083_0008, g32p_row03_traceSegment_056_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4100 8 9, g32p_row03_traceSegment_056_4100_0008, g32p_row03_traceSegment_056_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4083 17 17, g32p_row03_traceSegment_056_4083_0017, g32p_row03_traceSegment_056_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4050 33 34, g32p_row03_traceSegment_056_4050_0033, g32p_row03_traceSegment_056_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4117 8 9, g32p_row03_traceSegment_056_4117_0008, g32p_row03_traceSegment_056_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4134 8 9, g32p_row03_traceSegment_056_4134_0008, g32p_row03_traceSegment_056_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4117 17 17, g32p_row03_traceSegment_056_4117_0017, g32p_row03_traceSegment_056_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4151 8 9, g32p_row03_traceSegment_056_4151_0008, g32p_row03_traceSegment_056_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4168 8 9, g32p_row03_traceSegment_056_4168_0008, g32p_row03_traceSegment_056_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4151 17 17, g32p_row03_traceSegment_056_4151_0017, g32p_row03_traceSegment_056_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4117 34 34, g32p_row03_traceSegment_056_4117_0034, g32p_row03_traceSegment_056_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 4050 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4050 67 68, g32p_row03_traceSegment_056_4050_0067, g32p_row03_traceSegment_056_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_056 4185 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4201 8 9, g32p_row03_traceSegment_056_4201_0008, g32p_row03_traceSegment_056_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_056 4185 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4185 16 17, g32p_row03_traceSegment_056_4185_0016, g32p_row03_traceSegment_056_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4218 8 9, g32p_row03_traceSegment_056_4218_0008, g32p_row03_traceSegment_056_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4235 8 9, g32p_row03_traceSegment_056_4235_0008, g32p_row03_traceSegment_056_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4218 17 17, g32p_row03_traceSegment_056_4218_0017, g32p_row03_traceSegment_056_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_056 4185 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4185 33 34, g32p_row03_traceSegment_056_4185_0033, g32p_row03_traceSegment_056_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4252 8 9, g32p_row03_traceSegment_056_4252_0008, g32p_row03_traceSegment_056_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4269 8 9, g32p_row03_traceSegment_056_4269_0008, g32p_row03_traceSegment_056_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4252 17 17, g32p_row03_traceSegment_056_4252_0017, g32p_row03_traceSegment_056_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4286 8 9, g32p_row03_traceSegment_056_4286_0008, g32p_row03_traceSegment_056_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_056 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_056 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_056_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_056 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4303 8 9, g32p_row03_traceSegment_056_4303_0008, g32p_row03_traceSegment_056_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_056 4286 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4286 17 17, g32p_row03_traceSegment_056_4286_0017, g32p_row03_traceSegment_056_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_056 4252 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4252 34 34, g32p_row03_traceSegment_056_4252_0034, g32p_row03_traceSegment_056_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_056 4185 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4185 67 68, g32p_row03_traceSegment_056_4185_0067, g32p_row03_traceSegment_056_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_056_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_056 4050 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 4050 135 135, g32p_row03_traceSegment_056_4050_0135, g32p_row03_traceSegment_056_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_056 3780 540 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3780 270 270, g32p_row03_traceSegment_056_3780_0270, g32p_row03_traceSegment_056_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_056_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_056 3240 1080 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 3240 540 540, g32p_row03_traceSegment_056_3240_0540, g32p_row03_traceSegment_056_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_056_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_056 2160 2160 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 2160 1080 1080, g32p_row03_traceSegment_056_2160_1080, g32p_row03_traceSegment_056_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_056_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_056 0 4320 = [0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_056 0 2160 2160, g32p_row03_traceSegment_056_0000_2160, g32p_row03_traceSegment_056_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 56 = [0, 0, 40] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_056_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_057 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 57 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_057_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 16 8 9, g32p_row03_traceSegment_057_0016_0008, g32p_row03_traceSegment_057_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 0 16 17, g32p_row03_traceSegment_057_0000_0016, g32p_row03_traceSegment_057_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 33 8 9, g32p_row03_traceSegment_057_0033_0008, g32p_row03_traceSegment_057_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 58 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 50 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 50 8 9, g32p_row03_traceSegment_057_0050_0008, g32p_row03_traceSegment_057_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 33 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 33 17 17, g32p_row03_traceSegment_057_0033_0017, g32p_row03_traceSegment_057_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 0 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 0 33 34, g32p_row03_traceSegment_057_0000_0033, g32p_row03_traceSegment_057_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 67 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 75 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 67 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 67 8 9, g32p_row03_traceSegment_057_0067_0008, g32p_row03_traceSegment_057_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 84 8 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 92 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 84 17 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 84 8 9, g32p_row03_traceSegment_057_0084_0008, g32p_row03_traceSegment_057_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 67 34 = [0, 1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 67 17 17, g32p_row03_traceSegment_057_0067_0017, g32p_row03_traceSegment_057_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 101 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 109 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 101 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 101 8 9, g32p_row03_traceSegment_057_0101_0008, g32p_row03_traceSegment_057_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 118 8 9, g32p_row03_traceSegment_057_0118_0008, g32p_row03_traceSegment_057_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 101 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 101 17 17, g32p_row03_traceSegment_057_0101_0017, g32p_row03_traceSegment_057_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 67 68 = [0, 4, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 67 34 34, g32p_row03_traceSegment_057_0067_0034, g32p_row03_traceSegment_057_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 0 135 = [0, 4, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 0 67 68, g32p_row03_traceSegment_057_0000_0067, g32p_row03_traceSegment_057_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 135 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 159 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 151 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 151 8 9, g32p_row03_traceSegment_057_0151_0008, g32p_row03_traceSegment_057_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 135 33 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 135 16 17, g32p_row03_traceSegment_057_0135_0016, g32p_row03_traceSegment_057_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 176 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 168 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 168 8 9, g32p_row03_traceSegment_057_0168_0008, g32p_row03_traceSegment_057_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 185 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 185 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 185 8 9, g32p_row03_traceSegment_057_0185_0008, g32p_row03_traceSegment_057_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 168 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 168 17 17, g32p_row03_traceSegment_057_0168_0017, g32p_row03_traceSegment_057_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 135 67 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 135 33 34, g32p_row03_traceSegment_057_0135_0033, g32p_row03_traceSegment_057_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 202 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 210 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 202 17 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 202 8 9, g32p_row03_traceSegment_057_0202_0008, g32p_row03_traceSegment_057_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 219 8 9, g32p_row03_traceSegment_057_0219_0008, g32p_row03_traceSegment_057_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 202 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 202 17 17, g32p_row03_traceSegment_057_0202_0017, g32p_row03_traceSegment_057_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 236 8 9, g32p_row03_traceSegment_057_0236_0008, g32p_row03_traceSegment_057_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 261 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 253 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 253 8 9, g32p_row03_traceSegment_057_0253_0008, g32p_row03_traceSegment_057_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 236 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 236 17 17, g32p_row03_traceSegment_057_0236_0017, g32p_row03_traceSegment_057_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 202 68 = [0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 202 34 34, g32p_row03_traceSegment_057_0202_0034, g32p_row03_traceSegment_057_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 135 135 = [0, 1, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 135 67 68, g32p_row03_traceSegment_057_0135_0067, g32p_row03_traceSegment_057_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 0 270 = [0, 5, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 0 135 135, g32p_row03_traceSegment_057_0000_0135, g32p_row03_traceSegment_057_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 270 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 294 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 286 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 286 8 9, g32p_row03_traceSegment_057_0286_0008, g32p_row03_traceSegment_057_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 270 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 270 16 17, g32p_row03_traceSegment_057_0270_0016, g32p_row03_traceSegment_057_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 303 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 311 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 303 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 303 8 9, g32p_row03_traceSegment_057_0303_0008, g32p_row03_traceSegment_057_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 328 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 320 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 320 8 9, g32p_row03_traceSegment_057_0320_0008, g32p_row03_traceSegment_057_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 303 34 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 303 17 17, g32p_row03_traceSegment_057_0303_0017, g32p_row03_traceSegment_057_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 270 67 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 270 33 34, g32p_row03_traceSegment_057_0270_0033, g32p_row03_traceSegment_057_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 345 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 337 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 337 8 9, g32p_row03_traceSegment_057_0337_0008, g32p_row03_traceSegment_057_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 354 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 354 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 354 8 9, g32p_row03_traceSegment_057_0354_0008, g32p_row03_traceSegment_057_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 337 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 337 17 17, g32p_row03_traceSegment_057_0337_0017, g32p_row03_traceSegment_057_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 371 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 379 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 371 17 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 371 8 9, g32p_row03_traceSegment_057_0371_0008, g32p_row03_traceSegment_057_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 388 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 396 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 388 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 388 8 9, g32p_row03_traceSegment_057_0388_0008, g32p_row03_traceSegment_057_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 371 34 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 371 17 17, g32p_row03_traceSegment_057_0371_0017, g32p_row03_traceSegment_057_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 337 68 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 337 34 34, g32p_row03_traceSegment_057_0337_0034, g32p_row03_traceSegment_057_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 270 135 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 270 67 68, g32p_row03_traceSegment_057_0270_0067, g32p_row03_traceSegment_057_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 429 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 421 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 421 8 9, g32p_row03_traceSegment_057_0421_0008, g32p_row03_traceSegment_057_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 405 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 405 16 17, g32p_row03_traceSegment_057_0405_0016, g32p_row03_traceSegment_057_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 438 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 438 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 438 8 9, g32p_row03_traceSegment_057_0438_0008, g32p_row03_traceSegment_057_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 463 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 455 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 455 8 9, g32p_row03_traceSegment_057_0455_0008, g32p_row03_traceSegment_057_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 438 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 438 17 17, g32p_row03_traceSegment_057_0438_0017, g32p_row03_traceSegment_057_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 405 67 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 405 33 34, g32p_row03_traceSegment_057_0405_0033, g32p_row03_traceSegment_057_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 472 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 480 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 472 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 472 8 9, g32p_row03_traceSegment_057_0472_0008, g32p_row03_traceSegment_057_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 489 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 489 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 489 8 9, g32p_row03_traceSegment_057_0489_0008, g32p_row03_traceSegment_057_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 472 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 472 17 17, g32p_row03_traceSegment_057_0472_0017, g32p_row03_traceSegment_057_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 506 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 506 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 506 8 9, g32p_row03_traceSegment_057_0506_0008, g32p_row03_traceSegment_057_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 523 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 531 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 523 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 523 8 9, g32p_row03_traceSegment_057_0523_0008, g32p_row03_traceSegment_057_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 506 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 506 17 17, g32p_row03_traceSegment_057_0506_0017, g32p_row03_traceSegment_057_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 472 68 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 472 34 34, g32p_row03_traceSegment_057_0472_0034, g32p_row03_traceSegment_057_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 405 135 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 405 67 68, g32p_row03_traceSegment_057_0405_0067, g32p_row03_traceSegment_057_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 270 270 = [0, 15, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 270 135 135, g32p_row03_traceSegment_057_0270_0135, g32p_row03_traceSegment_057_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_057 0 540 = [0, 20, 0, 0, 25] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 0 270 270, g32p_row03_traceSegment_057_0000_0270, g32p_row03_traceSegment_057_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 540 16 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 564 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 556 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 556 8 9, g32p_row03_traceSegment_057_0556_0008, g32p_row03_traceSegment_057_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 540 33 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 540 16 17, g32p_row03_traceSegment_057_0540_0016, g32p_row03_traceSegment_057_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 573 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 581 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 573 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 573 8 9, g32p_row03_traceSegment_057_0573_0008, g32p_row03_traceSegment_057_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 598 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 590 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 590 8 9, g32p_row03_traceSegment_057_0590_0008, g32p_row03_traceSegment_057_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 573 34 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 573 17 17, g32p_row03_traceSegment_057_0573_0017, g32p_row03_traceSegment_057_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 540 67 = [0, 1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 540 33 34, g32p_row03_traceSegment_057_0540_0033, g32p_row03_traceSegment_057_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 607 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 615 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 607 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 607 8 9, g32p_row03_traceSegment_057_0607_0008, g32p_row03_traceSegment_057_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 624 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 624 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 624 8 9, g32p_row03_traceSegment_057_0624_0008, g32p_row03_traceSegment_057_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 607 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 607 17 17, g32p_row03_traceSegment_057_0607_0017, g32p_row03_traceSegment_057_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 641 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 649 9 = [0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 641 17 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 641 8 9, g32p_row03_traceSegment_057_0641_0008, g32p_row03_traceSegment_057_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 666 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 658 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 658 8 9, g32p_row03_traceSegment_057_0658_0008, g32p_row03_traceSegment_057_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 641 34 = [0, 1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 641 17 17, g32p_row03_traceSegment_057_0641_0017, g32p_row03_traceSegment_057_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 607 68 = [0, 1, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 607 34 34, g32p_row03_traceSegment_057_0607_0034, g32p_row03_traceSegment_057_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 540 135 = [0, 2, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 540 67 68, g32p_row03_traceSegment_057_0540_0067, g32p_row03_traceSegment_057_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 675 16 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 691 8 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 699 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 691 17 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 691 8 9, g32p_row03_traceSegment_057_0691_0008, g32p_row03_traceSegment_057_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 675 33 = [0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 675 16 17, g32p_row03_traceSegment_057_0675_0016, g32p_row03_traceSegment_057_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 708 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 716 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 708 17 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 708 8 9, g32p_row03_traceSegment_057_0708_0008, g32p_row03_traceSegment_057_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 725 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 733 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 725 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 725 8 9, g32p_row03_traceSegment_057_0725_0008, g32p_row03_traceSegment_057_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 708 34 = [0, 1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 708 17 17, g32p_row03_traceSegment_057_0708_0017, g32p_row03_traceSegment_057_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 675 67 = [0, 2, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 675 33 34, g32p_row03_traceSegment_057_0675_0033, g32p_row03_traceSegment_057_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 742 8 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 750 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 742 17 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 742 8 9, g32p_row03_traceSegment_057_0742_0008, g32p_row03_traceSegment_057_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 759 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 767 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 759 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 759 8 9, g32p_row03_traceSegment_057_0759_0008, g32p_row03_traceSegment_057_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 742 34 = [0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 742 17 17, g32p_row03_traceSegment_057_0742_0017, g32p_row03_traceSegment_057_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 776 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 776 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 776 8 9, g32p_row03_traceSegment_057_0776_0008, g32p_row03_traceSegment_057_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 793 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 801 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 793 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 793 8 9, g32p_row03_traceSegment_057_0793_0008, g32p_row03_traceSegment_057_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 776 34 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 776 17 17, g32p_row03_traceSegment_057_0776_0017, g32p_row03_traceSegment_057_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 742 68 = [0, 6, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 742 34 34, g32p_row03_traceSegment_057_0742_0034, g32p_row03_traceSegment_057_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 675 135 = [0, 8, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 675 67 68, g32p_row03_traceSegment_057_0675_0067, g32p_row03_traceSegment_057_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 540 270 = [0, 10, 0, 0, 28] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 540 135 135, g32p_row03_traceSegment_057_0540_0135, g32p_row03_traceSegment_057_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 810 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 834 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 826 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 826 8 9, g32p_row03_traceSegment_057_0826_0008, g32p_row03_traceSegment_057_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 810 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 810 16 17, g32p_row03_traceSegment_057_0810_0016, g32p_row03_traceSegment_057_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 851 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 843 17 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 843 8 9, g32p_row03_traceSegment_057_0843_0008, g32p_row03_traceSegment_057_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 860 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 868 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 860 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 860 8 9, g32p_row03_traceSegment_057_0860_0008, g32p_row03_traceSegment_057_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 843 34 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 843 17 17, g32p_row03_traceSegment_057_0843_0017, g32p_row03_traceSegment_057_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 810 67 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 810 33 34, g32p_row03_traceSegment_057_0810_0033, g32p_row03_traceSegment_057_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 877 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 877 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 877 8 9, g32p_row03_traceSegment_057_0877_0008, g32p_row03_traceSegment_057_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 902 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 894 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 894 8 9, g32p_row03_traceSegment_057_0894_0008, g32p_row03_traceSegment_057_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 877 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 877 17 17, g32p_row03_traceSegment_057_0877_0017, g32p_row03_traceSegment_057_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 919 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 911 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 911 8 9, g32p_row03_traceSegment_057_0911_0008, g32p_row03_traceSegment_057_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 928 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 936 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 928 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 928 8 9, g32p_row03_traceSegment_057_0928_0008, g32p_row03_traceSegment_057_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 911 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 911 17 17, g32p_row03_traceSegment_057_0911_0017, g32p_row03_traceSegment_057_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 877 68 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 877 34 34, g32p_row03_traceSegment_057_0877_0034, g32p_row03_traceSegment_057_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 810 135 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 810 67 68, g32p_row03_traceSegment_057_0810_0067, g32p_row03_traceSegment_057_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 961 8 = [0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 969 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 961 17 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 961 8 9, g32p_row03_traceSegment_057_0961_0008, g32p_row03_traceSegment_057_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 945 33 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 945 16 17, g32p_row03_traceSegment_057_0945_0016, g32p_row03_traceSegment_057_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 978 8 9, g32p_row03_traceSegment_057_0978_0008, g32p_row03_traceSegment_057_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1003 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 995 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 995 8 9, g32p_row03_traceSegment_057_0995_0008, g32p_row03_traceSegment_057_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 978 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 978 17 17, g32p_row03_traceSegment_057_0978_0017, g32p_row03_traceSegment_057_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 945 67 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 945 33 34, g32p_row03_traceSegment_057_0945_0033, g32p_row03_traceSegment_057_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1020 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1012 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1012 8 9, g32p_row03_traceSegment_057_1012_0008, g32p_row03_traceSegment_057_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1037 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1029 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1029 8 9, g32p_row03_traceSegment_057_1029_0008, g32p_row03_traceSegment_057_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1012 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1012 17 17, g32p_row03_traceSegment_057_1012_0017, g32p_row03_traceSegment_057_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1046 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1054 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1046 17 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1046 8 9, g32p_row03_traceSegment_057_1046_0008, g32p_row03_traceSegment_057_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1063 8 9, g32p_row03_traceSegment_057_1063_0008, g32p_row03_traceSegment_057_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1046 34 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1046 17 17, g32p_row03_traceSegment_057_1046_0017, g32p_row03_traceSegment_057_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 1012 68 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1012 34 34, g32p_row03_traceSegment_057_1012_0034, g32p_row03_traceSegment_057_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 945 135 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 945 67 68, g32p_row03_traceSegment_057_0945_0067, g32p_row03_traceSegment_057_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 810 270 = [0, 27] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 810 135 135, g32p_row03_traceSegment_057_0810_0135, g32p_row03_traceSegment_057_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_057 540 540 = [0, 37, 0, 0, 28] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 540 270 270, g32p_row03_traceSegment_057_0540_0270, g32p_row03_traceSegment_057_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_057 0 1080 = [0, 57, 0, 0, 53] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 0 540 540, g32p_row03_traceSegment_057_0000_0540, g32p_row03_traceSegment_057_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 1080 16 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1096 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1104 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1096 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1096 8 9, g32p_row03_traceSegment_057_1096_0008, g32p_row03_traceSegment_057_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 1080 33 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1080 16 17, g32p_row03_traceSegment_057_1080_0016, g32p_row03_traceSegment_057_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1113 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1113 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1113 8 9, g32p_row03_traceSegment_057_1113_0008, g32p_row03_traceSegment_057_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1138 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1130 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1130 8 9, g32p_row03_traceSegment_057_1130_0008, g32p_row03_traceSegment_057_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1113 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1113 17 17, g32p_row03_traceSegment_057_1113_0017, g32p_row03_traceSegment_057_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 1080 67 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1080 33 34, g32p_row03_traceSegment_057_1080_0033, g32p_row03_traceSegment_057_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1155 9 = [0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1147 17 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1147 8 9, g32p_row03_traceSegment_057_1147_0008, g32p_row03_traceSegment_057_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1172 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1164 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1164 8 9, g32p_row03_traceSegment_057_1164_0008, g32p_row03_traceSegment_057_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1147 34 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1147 17 17, g32p_row03_traceSegment_057_1147_0017, g32p_row03_traceSegment_057_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1181 8 9, g32p_row03_traceSegment_057_1181_0008, g32p_row03_traceSegment_057_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1206 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1198 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1198 8 9, g32p_row03_traceSegment_057_1198_0008, g32p_row03_traceSegment_057_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1181 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1181 17 17, g32p_row03_traceSegment_057_1181_0017, g32p_row03_traceSegment_057_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 1147 68 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1147 34 34, g32p_row03_traceSegment_057_1147_0034, g32p_row03_traceSegment_057_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 1080 135 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1080 67 68, g32p_row03_traceSegment_057_1080_0067, g32p_row03_traceSegment_057_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1231 8 9, g32p_row03_traceSegment_057_1231_0008, g32p_row03_traceSegment_057_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1215 16 17, g32p_row03_traceSegment_057_1215_0016, g32p_row03_traceSegment_057_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1256 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1248 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1248 8 9, g32p_row03_traceSegment_057_1248_0008, g32p_row03_traceSegment_057_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1265 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1265 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1265 8 9, g32p_row03_traceSegment_057_1265_0008, g32p_row03_traceSegment_057_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1248 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1248 17 17, g32p_row03_traceSegment_057_1248_0017, g32p_row03_traceSegment_057_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 1215 67 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1215 33 34, g32p_row03_traceSegment_057_1215_0033, g32p_row03_traceSegment_057_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1282 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1282 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1282 8 9, g32p_row03_traceSegment_057_1282_0008, g32p_row03_traceSegment_057_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1299 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1307 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1299 17 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1299 8 9, g32p_row03_traceSegment_057_1299_0008, g32p_row03_traceSegment_057_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1282 34 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1282 17 17, g32p_row03_traceSegment_057_1282_0017, g32p_row03_traceSegment_057_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1316 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1316 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1316 8 9, g32p_row03_traceSegment_057_1316_0008, g32p_row03_traceSegment_057_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1333 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1341 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1333 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1333 8 9, g32p_row03_traceSegment_057_1333_0008, g32p_row03_traceSegment_057_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1316 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1316 17 17, g32p_row03_traceSegment_057_1316_0017, g32p_row03_traceSegment_057_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 1282 68 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1282 34 34, g32p_row03_traceSegment_057_1282_0034, g32p_row03_traceSegment_057_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 1215 135 = [0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1215 67 68, g32p_row03_traceSegment_057_1215_0067, g32p_row03_traceSegment_057_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 1080 270 = [0, 15, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1080 135 135, g32p_row03_traceSegment_057_1080_0135, g32p_row03_traceSegment_057_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 1350 16 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1366 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1374 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1366 17 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1366 8 9, g32p_row03_traceSegment_057_1366_0008, g32p_row03_traceSegment_057_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 1350 33 = [0, 1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1350 16 17, g32p_row03_traceSegment_057_1350_0016, g32p_row03_traceSegment_057_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1391 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1383 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1383 8 9, g32p_row03_traceSegment_057_1383_0008, g32p_row03_traceSegment_057_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1400 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1408 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1400 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1400 8 9, g32p_row03_traceSegment_057_1400_0008, g32p_row03_traceSegment_057_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1383 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1383 17 17, g32p_row03_traceSegment_057_1383_0017, g32p_row03_traceSegment_057_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 1350 67 = [0, 1, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1350 33 34, g32p_row03_traceSegment_057_1350_0033, g32p_row03_traceSegment_057_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1417 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1417 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1417 8 9, g32p_row03_traceSegment_057_1417_0008, g32p_row03_traceSegment_057_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1442 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1434 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1434 8 9, g32p_row03_traceSegment_057_1434_0008, g32p_row03_traceSegment_057_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1417 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1417 17 17, g32p_row03_traceSegment_057_1417_0017, g32p_row03_traceSegment_057_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1451 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1451 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1451 8 9, g32p_row03_traceSegment_057_1451_0008, g32p_row03_traceSegment_057_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1468 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1476 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1468 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1468 8 9, g32p_row03_traceSegment_057_1468_0008, g32p_row03_traceSegment_057_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1451 34 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1451 17 17, g32p_row03_traceSegment_057_1451_0017, g32p_row03_traceSegment_057_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 1417 68 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1417 34 34, g32p_row03_traceSegment_057_1417_0034, g32p_row03_traceSegment_057_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 1350 135 = [0, 1, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1350 67 68, g32p_row03_traceSegment_057_1350_0067, g32p_row03_traceSegment_057_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1501 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1501 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1501 8 9, g32p_row03_traceSegment_057_1501_0008, g32p_row03_traceSegment_057_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 1485 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1485 16 17, g32p_row03_traceSegment_057_1485_0016, g32p_row03_traceSegment_057_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1526 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1518 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1518 8 9, g32p_row03_traceSegment_057_1518_0008, g32p_row03_traceSegment_057_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1535 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1543 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1535 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1535 8 9, g32p_row03_traceSegment_057_1535_0008, g32p_row03_traceSegment_057_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1518 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1518 17 17, g32p_row03_traceSegment_057_1518_0017, g32p_row03_traceSegment_057_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 1485 67 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1485 33 34, g32p_row03_traceSegment_057_1485_0033, g32p_row03_traceSegment_057_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1552 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1560 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1552 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1552 8 9, g32p_row03_traceSegment_057_1552_0008, g32p_row03_traceSegment_057_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1569 8 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1577 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1569 17 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1569 8 9, g32p_row03_traceSegment_057_1569_0008, g32p_row03_traceSegment_057_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1552 34 = [0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1552 17 17, g32p_row03_traceSegment_057_1552_0017, g32p_row03_traceSegment_057_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1594 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1586 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1586 8 9, g32p_row03_traceSegment_057_1586_0008, g32p_row03_traceSegment_057_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1603 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1611 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1603 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1603 8 9, g32p_row03_traceSegment_057_1603_0008, g32p_row03_traceSegment_057_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1586 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1586 17 17, g32p_row03_traceSegment_057_1586_0017, g32p_row03_traceSegment_057_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 1552 68 = [0, 2, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1552 34 34, g32p_row03_traceSegment_057_1552_0034, g32p_row03_traceSegment_057_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 1485 135 = [0, 2, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1485 67 68, g32p_row03_traceSegment_057_1485_0067, g32p_row03_traceSegment_057_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 1350 270 = [0, 3, 0, 0, 26] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1350 135 135, g32p_row03_traceSegment_057_1350_0135, g32p_row03_traceSegment_057_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_057 1080 540 = [0, 18, 0, 0, 37] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1080 270 270, g32p_row03_traceSegment_057_1080_0270, g32p_row03_traceSegment_057_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 1620 16 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1636 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1636 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1636 8 9, g32p_row03_traceSegment_057_1636_0008, g32p_row03_traceSegment_057_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 1620 33 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1620 16 17, g32p_row03_traceSegment_057_1620_0016, g32p_row03_traceSegment_057_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1661 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1653 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1653 8 9, g32p_row03_traceSegment_057_1653_0008, g32p_row03_traceSegment_057_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1670 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1678 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1670 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1670 8 9, g32p_row03_traceSegment_057_1670_0008, g32p_row03_traceSegment_057_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1653 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1653 17 17, g32p_row03_traceSegment_057_1653_0017, g32p_row03_traceSegment_057_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 1620 67 = [0, 1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1620 33 34, g32p_row03_traceSegment_057_1620_0033, g32p_row03_traceSegment_057_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1695 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1687 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1687 8 9, g32p_row03_traceSegment_057_1687_0008, g32p_row03_traceSegment_057_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1704 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1712 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1704 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1704 8 9, g32p_row03_traceSegment_057_1704_0008, g32p_row03_traceSegment_057_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1687 34 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1687 17 17, g32p_row03_traceSegment_057_1687_0017, g32p_row03_traceSegment_057_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1721 8 9, g32p_row03_traceSegment_057_1721_0008, g32p_row03_traceSegment_057_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1738 8 9, g32p_row03_traceSegment_057_1738_0008, g32p_row03_traceSegment_057_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1721 17 17, g32p_row03_traceSegment_057_1721_0017, g32p_row03_traceSegment_057_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 1687 68 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1687 34 34, g32p_row03_traceSegment_057_1687_0034, g32p_row03_traceSegment_057_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 1620 135 = [0, 2, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1620 67 68, g32p_row03_traceSegment_057_1620_0067, g32p_row03_traceSegment_057_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1771 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1771 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1771 8 9, g32p_row03_traceSegment_057_1771_0008, g32p_row03_traceSegment_057_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 1755 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1755 16 17, g32p_row03_traceSegment_057_1755_0016, g32p_row03_traceSegment_057_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1796 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1788 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1788 8 9, g32p_row03_traceSegment_057_1788_0008, g32p_row03_traceSegment_057_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1805 8 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1813 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1805 17 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1805 8 9, g32p_row03_traceSegment_057_1805_0008, g32p_row03_traceSegment_057_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1788 34 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1788 17 17, g32p_row03_traceSegment_057_1788_0017, g32p_row03_traceSegment_057_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 1755 67 = [0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1755 33 34, g32p_row03_traceSegment_057_1755_0033, g32p_row03_traceSegment_057_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1822 8 9, g32p_row03_traceSegment_057_1822_0008, g32p_row03_traceSegment_057_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1839 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1839 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1839 8 9, g32p_row03_traceSegment_057_1839_0008, g32p_row03_traceSegment_057_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1822 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1822 17 17, g32p_row03_traceSegment_057_1822_0017, g32p_row03_traceSegment_057_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1864 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1856 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1856 8 9, g32p_row03_traceSegment_057_1856_0008, g32p_row03_traceSegment_057_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1873 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1881 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1873 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1873 8 9, g32p_row03_traceSegment_057_1873_0008, g32p_row03_traceSegment_057_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1856 34 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1856 17 17, g32p_row03_traceSegment_057_1856_0017, g32p_row03_traceSegment_057_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 1822 68 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1822 34 34, g32p_row03_traceSegment_057_1822_0034, g32p_row03_traceSegment_057_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 1755 135 = [0, 3, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1755 67 68, g32p_row03_traceSegment_057_1755_0067, g32p_row03_traceSegment_057_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 1620 270 = [0, 5, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1620 135 135, g32p_row03_traceSegment_057_1620_0135, g32p_row03_traceSegment_057_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1906 8 9, g32p_row03_traceSegment_057_1906_0008, g32p_row03_traceSegment_057_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1890 16 17, g32p_row03_traceSegment_057_1890_0016, g32p_row03_traceSegment_057_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1923 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1923 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1923 8 9, g32p_row03_traceSegment_057_1923_0008, g32p_row03_traceSegment_057_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1940 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1948 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1940 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1940 8 9, g32p_row03_traceSegment_057_1940_0008, g32p_row03_traceSegment_057_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1923 34 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1923 17 17, g32p_row03_traceSegment_057_1923_0017, g32p_row03_traceSegment_057_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 1890 67 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1890 33 34, g32p_row03_traceSegment_057_1890_0033, g32p_row03_traceSegment_057_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1957 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1957 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1957 8 9, g32p_row03_traceSegment_057_1957_0008, g32p_row03_traceSegment_057_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1982 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1974 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1974 8 9, g32p_row03_traceSegment_057_1974_0008, g32p_row03_traceSegment_057_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1957 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1957 17 17, g32p_row03_traceSegment_057_1957_0017, g32p_row03_traceSegment_057_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 1991 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 1991 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1991 8 9, g32p_row03_traceSegment_057_1991_0008, g32p_row03_traceSegment_057_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2016 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2008 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2008 8 9, g32p_row03_traceSegment_057_2008_0008, g32p_row03_traceSegment_057_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 1991 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1991 17 17, g32p_row03_traceSegment_057_1991_0017, g32p_row03_traceSegment_057_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 1957 68 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1957 34 34, g32p_row03_traceSegment_057_1957_0034, g32p_row03_traceSegment_057_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 1890 135 = [0, 6, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1890 67 68, g32p_row03_traceSegment_057_1890_0067, g32p_row03_traceSegment_057_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2041 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2041 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2041 8 9, g32p_row03_traceSegment_057_2041_0008, g32p_row03_traceSegment_057_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 2025 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2025 16 17, g32p_row03_traceSegment_057_2025_0016, g32p_row03_traceSegment_057_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2058 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2066 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2058 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2058 8 9, g32p_row03_traceSegment_057_2058_0008, g32p_row03_traceSegment_057_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2075 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2083 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2075 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2075 8 9, g32p_row03_traceSegment_057_2075_0008, g32p_row03_traceSegment_057_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2058 34 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2058 17 17, g32p_row03_traceSegment_057_2058_0017, g32p_row03_traceSegment_057_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 2025 67 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2025 33 34, g32p_row03_traceSegment_057_2025_0033, g32p_row03_traceSegment_057_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2092 8 9, g32p_row03_traceSegment_057_2092_0008, g32p_row03_traceSegment_057_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2117 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2109 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2109 8 9, g32p_row03_traceSegment_057_2109_0008, g32p_row03_traceSegment_057_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2092 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2092 17 17, g32p_row03_traceSegment_057_2092_0017, g32p_row03_traceSegment_057_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2126 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2126 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2126 8 9, g32p_row03_traceSegment_057_2126_0008, g32p_row03_traceSegment_057_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2143 8 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2151 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2143 17 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2143 8 9, g32p_row03_traceSegment_057_2143_0008, g32p_row03_traceSegment_057_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2126 34 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2126 17 17, g32p_row03_traceSegment_057_2126_0017, g32p_row03_traceSegment_057_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 2092 68 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2092 34 34, g32p_row03_traceSegment_057_2092_0034, g32p_row03_traceSegment_057_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 2025 135 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2025 67 68, g32p_row03_traceSegment_057_2025_0067, g32p_row03_traceSegment_057_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 1890 270 = [0, 19, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1890 135 135, g32p_row03_traceSegment_057_1890_0135, g32p_row03_traceSegment_057_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_057 1620 540 = [0, 24, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1620 270 270, g32p_row03_traceSegment_057_1620_0270, g32p_row03_traceSegment_057_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_057_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_057 1080 1080 = [0, 42, 0, 0, 51] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 1080 540 540, g32p_row03_traceSegment_057_1080_0540, g32p_row03_traceSegment_057_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_057 0 2160 = [0, 99, 0, 0, 104] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 0 1080 1080, g32p_row03_traceSegment_057_0000_1080, g32p_row03_traceSegment_057_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 2160 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2184 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2176 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2176 8 9, g32p_row03_traceSegment_057_2176_0008, g32p_row03_traceSegment_057_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 2160 33 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2160 16 17, g32p_row03_traceSegment_057_2160_0016, g32p_row03_traceSegment_057_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2201 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2193 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2193 8 9, g32p_row03_traceSegment_057_2193_0008, g32p_row03_traceSegment_057_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2210 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2210 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2210 8 9, g32p_row03_traceSegment_057_2210_0008, g32p_row03_traceSegment_057_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2193 34 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2193 17 17, g32p_row03_traceSegment_057_2193_0017, g32p_row03_traceSegment_057_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 2160 67 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2160 33 34, g32p_row03_traceSegment_057_2160_0033, g32p_row03_traceSegment_057_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2227 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2235 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2227 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2227 8 9, g32p_row03_traceSegment_057_2227_0008, g32p_row03_traceSegment_057_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2252 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2244 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2244 8 9, g32p_row03_traceSegment_057_2244_0008, g32p_row03_traceSegment_057_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2227 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2227 17 17, g32p_row03_traceSegment_057_2227_0017, g32p_row03_traceSegment_057_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2269 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2261 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2261 8 9, g32p_row03_traceSegment_057_2261_0008, g32p_row03_traceSegment_057_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2278 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2286 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2278 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2278 8 9, g32p_row03_traceSegment_057_2278_0008, g32p_row03_traceSegment_057_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2261 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2261 17 17, g32p_row03_traceSegment_057_2261_0017, g32p_row03_traceSegment_057_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 2227 68 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2227 34 34, g32p_row03_traceSegment_057_2227_0034, g32p_row03_traceSegment_057_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 2160 135 = [0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2160 67 68, g32p_row03_traceSegment_057_2160_0067, g32p_row03_traceSegment_057_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 2295 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2311 8 9, g32p_row03_traceSegment_057_2311_0008, g32p_row03_traceSegment_057_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 2295 33 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2295 16 17, g32p_row03_traceSegment_057_2295_0016, g32p_row03_traceSegment_057_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2336 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2328 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2328 8 9, g32p_row03_traceSegment_057_2328_0008, g32p_row03_traceSegment_057_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2345 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2353 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2345 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2345 8 9, g32p_row03_traceSegment_057_2345_0008, g32p_row03_traceSegment_057_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2328 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2328 17 17, g32p_row03_traceSegment_057_2328_0017, g32p_row03_traceSegment_057_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 2295 67 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2295 33 34, g32p_row03_traceSegment_057_2295_0033, g32p_row03_traceSegment_057_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2362 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2370 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2362 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2362 8 9, g32p_row03_traceSegment_057_2362_0008, g32p_row03_traceSegment_057_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2379 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2387 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2379 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2379 8 9, g32p_row03_traceSegment_057_2379_0008, g32p_row03_traceSegment_057_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2362 34 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2362 17 17, g32p_row03_traceSegment_057_2362_0017, g32p_row03_traceSegment_057_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2396 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2404 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2396 17 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2396 8 9, g32p_row03_traceSegment_057_2396_0008, g32p_row03_traceSegment_057_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2421 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2413 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2413 8 9, g32p_row03_traceSegment_057_2413_0008, g32p_row03_traceSegment_057_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2396 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2396 17 17, g32p_row03_traceSegment_057_2396_0017, g32p_row03_traceSegment_057_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 2362 68 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2362 34 34, g32p_row03_traceSegment_057_2362_0034, g32p_row03_traceSegment_057_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 2295 135 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2295 67 68, g32p_row03_traceSegment_057_2295_0067, g32p_row03_traceSegment_057_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 2160 270 = [0, 31] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2160 135 135, g32p_row03_traceSegment_057_2160_0135, g32p_row03_traceSegment_057_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 2430 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2446 8 9, g32p_row03_traceSegment_057_2446_0008, g32p_row03_traceSegment_057_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 2430 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2430 16 17, g32p_row03_traceSegment_057_2430_0016, g32p_row03_traceSegment_057_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2463 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2463 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2463 8 9, g32p_row03_traceSegment_057_2463_0008, g32p_row03_traceSegment_057_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2480 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2480 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2480 8 9, g32p_row03_traceSegment_057_2480_0008, g32p_row03_traceSegment_057_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2463 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2463 17 17, g32p_row03_traceSegment_057_2463_0017, g32p_row03_traceSegment_057_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 2430 67 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2430 33 34, g32p_row03_traceSegment_057_2430_0033, g32p_row03_traceSegment_057_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2505 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2497 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2497 8 9, g32p_row03_traceSegment_057_2497_0008, g32p_row03_traceSegment_057_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2514 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2522 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2514 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2514 8 9, g32p_row03_traceSegment_057_2514_0008, g32p_row03_traceSegment_057_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2497 34 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2497 17 17, g32p_row03_traceSegment_057_2497_0017, g32p_row03_traceSegment_057_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2531 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2531 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2531 8 9, g32p_row03_traceSegment_057_2531_0008, g32p_row03_traceSegment_057_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2548 8 9, g32p_row03_traceSegment_057_2548_0008, g32p_row03_traceSegment_057_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2531 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2531 17 17, g32p_row03_traceSegment_057_2531_0017, g32p_row03_traceSegment_057_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 2497 68 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2497 34 34, g32p_row03_traceSegment_057_2497_0034, g32p_row03_traceSegment_057_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 2430 135 = [0, 5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2430 67 68, g32p_row03_traceSegment_057_2430_0067, g32p_row03_traceSegment_057_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2589 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2581 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2581 8 9, g32p_row03_traceSegment_057_2581_0008, g32p_row03_traceSegment_057_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 2565 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2565 16 17, g32p_row03_traceSegment_057_2565_0016, g32p_row03_traceSegment_057_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2598 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2606 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2598 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2598 8 9, g32p_row03_traceSegment_057_2598_0008, g32p_row03_traceSegment_057_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2615 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2623 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2615 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2615 8 9, g32p_row03_traceSegment_057_2615_0008, g32p_row03_traceSegment_057_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2598 34 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2598 17 17, g32p_row03_traceSegment_057_2598_0017, g32p_row03_traceSegment_057_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 2565 67 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2565 33 34, g32p_row03_traceSegment_057_2565_0033, g32p_row03_traceSegment_057_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2632 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2640 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2632 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2632 8 9, g32p_row03_traceSegment_057_2632_0008, g32p_row03_traceSegment_057_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2649 8 9, g32p_row03_traceSegment_057_2649_0008, g32p_row03_traceSegment_057_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2632 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2632 17 17, g32p_row03_traceSegment_057_2632_0017, g32p_row03_traceSegment_057_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2666 8 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2666 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2666 8 9, g32p_row03_traceSegment_057_2666_0008, g32p_row03_traceSegment_057_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2691 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2683 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2683 8 9, g32p_row03_traceSegment_057_2683_0008, g32p_row03_traceSegment_057_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2666 34 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2666 17 17, g32p_row03_traceSegment_057_2666_0017, g32p_row03_traceSegment_057_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 2632 68 = [0, 5, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2632 34 34, g32p_row03_traceSegment_057_2632_0034, g32p_row03_traceSegment_057_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 2565 135 = [0, 10, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2565 67 68, g32p_row03_traceSegment_057_2565_0067, g32p_row03_traceSegment_057_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 2430 270 = [0, 15, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2430 135 135, g32p_row03_traceSegment_057_2430_0135, g32p_row03_traceSegment_057_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_057 2160 540 = [0, 46, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2160 270 270, g32p_row03_traceSegment_057_2160_0270, g32p_row03_traceSegment_057_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 2700 16 = [0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2716 8 9, g32p_row03_traceSegment_057_2716_0008, g32p_row03_traceSegment_057_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 2700 33 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2700 16 17, g32p_row03_traceSegment_057_2700_0016, g32p_row03_traceSegment_057_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2733 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2733 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2733 8 9, g32p_row03_traceSegment_057_2733_0008, g32p_row03_traceSegment_057_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2758 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2750 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2750 8 9, g32p_row03_traceSegment_057_2750_0008, g32p_row03_traceSegment_057_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2733 34 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2733 17 17, g32p_row03_traceSegment_057_2733_0017, g32p_row03_traceSegment_057_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 2700 67 = [0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2700 33 34, g32p_row03_traceSegment_057_2700_0033, g32p_row03_traceSegment_057_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2767 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2775 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2767 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2767 8 9, g32p_row03_traceSegment_057_2767_0008, g32p_row03_traceSegment_057_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2784 8 9, g32p_row03_traceSegment_057_2784_0008, g32p_row03_traceSegment_057_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2767 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2767 17 17, g32p_row03_traceSegment_057_2767_0017, g32p_row03_traceSegment_057_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2801 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2801 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2801 8 9, g32p_row03_traceSegment_057_2801_0008, g32p_row03_traceSegment_057_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2826 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2818 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2818 8 9, g32p_row03_traceSegment_057_2818_0008, g32p_row03_traceSegment_057_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2801 34 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2801 17 17, g32p_row03_traceSegment_057_2801_0017, g32p_row03_traceSegment_057_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 2767 68 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2767 34 34, g32p_row03_traceSegment_057_2767_0034, g32p_row03_traceSegment_057_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 2700 135 = [0, 5, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2700 67 68, g32p_row03_traceSegment_057_2700_0067, g32p_row03_traceSegment_057_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2851 8 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2851 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2851 8 9, g32p_row03_traceSegment_057_2851_0008, g32p_row03_traceSegment_057_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 2835 33 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2835 16 17, g32p_row03_traceSegment_057_2835_0016, g32p_row03_traceSegment_057_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2868 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2876 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2868 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2868 8 9, g32p_row03_traceSegment_057_2868_0008, g32p_row03_traceSegment_057_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2885 8 9, g32p_row03_traceSegment_057_2885_0008, g32p_row03_traceSegment_057_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2868 34 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2868 17 17, g32p_row03_traceSegment_057_2868_0017, g32p_row03_traceSegment_057_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 2835 67 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2835 33 34, g32p_row03_traceSegment_057_2835_0033, g32p_row03_traceSegment_057_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2902 8 9, g32p_row03_traceSegment_057_2902_0008, g32p_row03_traceSegment_057_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2927 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2919 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2919 8 9, g32p_row03_traceSegment_057_2919_0008, g32p_row03_traceSegment_057_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2902 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2902 17 17, g32p_row03_traceSegment_057_2902_0017, g32p_row03_traceSegment_057_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2944 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2936 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2936 8 9, g32p_row03_traceSegment_057_2936_0008, g32p_row03_traceSegment_057_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2953 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2953 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2953 8 9, g32p_row03_traceSegment_057_2953_0008, g32p_row03_traceSegment_057_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 2936 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2936 17 17, g32p_row03_traceSegment_057_2936_0017, g32p_row03_traceSegment_057_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 2902 68 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2902 34 34, g32p_row03_traceSegment_057_2902_0034, g32p_row03_traceSegment_057_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 2835 135 = [0, 2, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2835 67 68, g32p_row03_traceSegment_057_2835_0067, g32p_row03_traceSegment_057_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 2700 270 = [0, 7, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2700 135 135, g32p_row03_traceSegment_057_2700_0135, g32p_row03_traceSegment_057_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 2970 16 = [0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 2986 8 = [0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 2986 17 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2986 8 9, g32p_row03_traceSegment_057_2986_0008, g32p_row03_traceSegment_057_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 2970 33 = [0, 1, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2970 16 17, g32p_row03_traceSegment_057_2970_0016, g32p_row03_traceSegment_057_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3003 8 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3011 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3003 17 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3003 8 9, g32p_row03_traceSegment_057_3003_0008, g32p_row03_traceSegment_057_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3020 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3020 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3020 8 9, g32p_row03_traceSegment_057_3020_0008, g32p_row03_traceSegment_057_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3003 34 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3003 17 17, g32p_row03_traceSegment_057_3003_0017, g32p_row03_traceSegment_057_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 2970 67 = [0, 2, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2970 33 34, g32p_row03_traceSegment_057_2970_0033, g32p_row03_traceSegment_057_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3037 8 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3045 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3037 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3037 8 9, g32p_row03_traceSegment_057_3037_0008, g32p_row03_traceSegment_057_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3054 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3062 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3054 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3054 8 9, g32p_row03_traceSegment_057_3054_0008, g32p_row03_traceSegment_057_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3037 34 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3037 17 17, g32p_row03_traceSegment_057_3037_0017, g32p_row03_traceSegment_057_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3079 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3071 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3071 8 9, g32p_row03_traceSegment_057_3071_0008, g32p_row03_traceSegment_057_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3096 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3088 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3088 8 9, g32p_row03_traceSegment_057_3088_0008, g32p_row03_traceSegment_057_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3071 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3071 17 17, g32p_row03_traceSegment_057_3071_0017, g32p_row03_traceSegment_057_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 3037 68 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3037 34 34, g32p_row03_traceSegment_057_3037_0034, g32p_row03_traceSegment_057_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 2970 135 = [0, 2, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2970 67 68, g32p_row03_traceSegment_057_2970_0067, g32p_row03_traceSegment_057_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3121 8 9, g32p_row03_traceSegment_057_3121_0008, g32p_row03_traceSegment_057_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3105 16 17, g32p_row03_traceSegment_057_3105_0016, g32p_row03_traceSegment_057_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3138 8 9, g32p_row03_traceSegment_057_3138_0008, g32p_row03_traceSegment_057_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3155 8 9, g32p_row03_traceSegment_057_3155_0008, g32p_row03_traceSegment_057_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3138 17 17, g32p_row03_traceSegment_057_3138_0017, g32p_row03_traceSegment_057_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3105 33 34, g32p_row03_traceSegment_057_3105_0033, g32p_row03_traceSegment_057_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3172 8 9, g32p_row03_traceSegment_057_3172_0008, g32p_row03_traceSegment_057_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3189 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3197 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3189 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3189 8 9, g32p_row03_traceSegment_057_3189_0008, g32p_row03_traceSegment_057_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3172 34 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3172 17 17, g32p_row03_traceSegment_057_3172_0017, g32p_row03_traceSegment_057_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3206 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3206 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3206 8 9, g32p_row03_traceSegment_057_3206_0008, g32p_row03_traceSegment_057_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3231 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3223 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3223 8 9, g32p_row03_traceSegment_057_3223_0008, g32p_row03_traceSegment_057_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3206 34 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3206 17 17, g32p_row03_traceSegment_057_3206_0017, g32p_row03_traceSegment_057_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 3172 68 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3172 34 34, g32p_row03_traceSegment_057_3172_0034, g32p_row03_traceSegment_057_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 3105 135 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3105 67 68, g32p_row03_traceSegment_057_3105_0067, g32p_row03_traceSegment_057_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 2970 270 = [0, 4, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2970 135 135, g32p_row03_traceSegment_057_2970_0135, g32p_row03_traceSegment_057_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_057 2700 540 = [0, 11, 0, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2700 270 270, g32p_row03_traceSegment_057_2700_0270, g32p_row03_traceSegment_057_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_057 2160 1080 = [0, 57, 0, 0, 33] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2160 540 540, g32p_row03_traceSegment_057_2160_0540, g32p_row03_traceSegment_057_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3256 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3264 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3256 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3256 8 9, g32p_row03_traceSegment_057_3256_0008, g32p_row03_traceSegment_057_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 3240 33 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3240 16 17, g32p_row03_traceSegment_057_3240_0016, g32p_row03_traceSegment_057_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3281 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3273 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3273 8 9, g32p_row03_traceSegment_057_3273_0008, g32p_row03_traceSegment_057_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3290 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3298 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3290 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3290 8 9, g32p_row03_traceSegment_057_3290_0008, g32p_row03_traceSegment_057_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3273 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3273 17 17, g32p_row03_traceSegment_057_3273_0017, g32p_row03_traceSegment_057_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 3240 67 = [0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3240 33 34, g32p_row03_traceSegment_057_3240_0033, g32p_row03_traceSegment_057_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3307 8 9, g32p_row03_traceSegment_057_3307_0008, g32p_row03_traceSegment_057_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3332 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3324 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3324 8 9, g32p_row03_traceSegment_057_3324_0008, g32p_row03_traceSegment_057_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3307 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3307 17 17, g32p_row03_traceSegment_057_3307_0017, g32p_row03_traceSegment_057_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3341 8 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3341 17 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3341 8 9, g32p_row03_traceSegment_057_3341_0008, g32p_row03_traceSegment_057_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3358 8 9, g32p_row03_traceSegment_057_3358_0008, g32p_row03_traceSegment_057_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3341 34 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3341 17 17, g32p_row03_traceSegment_057_3341_0017, g32p_row03_traceSegment_057_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 3307 68 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3307 34 34, g32p_row03_traceSegment_057_3307_0034, g32p_row03_traceSegment_057_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 3240 135 = [0, 2, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3240 67 68, g32p_row03_traceSegment_057_3240_0067, g32p_row03_traceSegment_057_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3391 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3391 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3391 8 9, g32p_row03_traceSegment_057_3391_0008, g32p_row03_traceSegment_057_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 3375 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3375 16 17, g32p_row03_traceSegment_057_3375_0016, g32p_row03_traceSegment_057_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3408 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3408 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3408 8 9, g32p_row03_traceSegment_057_3408_0008, g32p_row03_traceSegment_057_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3425 8 9, g32p_row03_traceSegment_057_3425_0008, g32p_row03_traceSegment_057_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3408 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3408 17 17, g32p_row03_traceSegment_057_3408_0017, g32p_row03_traceSegment_057_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 3375 67 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3375 33 34, g32p_row03_traceSegment_057_3375_0033, g32p_row03_traceSegment_057_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3442 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3450 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3442 17 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3442 8 9, g32p_row03_traceSegment_057_3442_0008, g32p_row03_traceSegment_057_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3459 8 9, g32p_row03_traceSegment_057_3459_0008, g32p_row03_traceSegment_057_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3442 34 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3442 17 17, g32p_row03_traceSegment_057_3442_0017, g32p_row03_traceSegment_057_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3476 8 9, g32p_row03_traceSegment_057_3476_0008, g32p_row03_traceSegment_057_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3493 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3493 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3493 8 9, g32p_row03_traceSegment_057_3493_0008, g32p_row03_traceSegment_057_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3476 34 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3476 17 17, g32p_row03_traceSegment_057_3476_0017, g32p_row03_traceSegment_057_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 3442 68 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3442 34 34, g32p_row03_traceSegment_057_3442_0034, g32p_row03_traceSegment_057_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 3375 135 = [0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3375 67 68, g32p_row03_traceSegment_057_3375_0067, g32p_row03_traceSegment_057_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 3240 270 = [0, 5, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3240 135 135, g32p_row03_traceSegment_057_3240_0135, g32p_row03_traceSegment_057_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 3510 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3526 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3526 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3526 8 9, g32p_row03_traceSegment_057_3526_0008, g32p_row03_traceSegment_057_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 3510 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3510 16 17, g32p_row03_traceSegment_057_3510_0016, g32p_row03_traceSegment_057_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3543 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3551 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3543 17 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3543 8 9, g32p_row03_traceSegment_057_3543_0008, g32p_row03_traceSegment_057_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3560 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3568 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3560 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3560 8 9, g32p_row03_traceSegment_057_3560_0008, g32p_row03_traceSegment_057_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3543 34 = [0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3543 17 17, g32p_row03_traceSegment_057_3543_0017, g32p_row03_traceSegment_057_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 3510 67 = [0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3510 33 34, g32p_row03_traceSegment_057_3510_0033, g32p_row03_traceSegment_057_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3585 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3577 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3577 8 9, g32p_row03_traceSegment_057_3577_0008, g32p_row03_traceSegment_057_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3594 8 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3602 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3594 17 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3594 8 9, g32p_row03_traceSegment_057_3594_0008, g32p_row03_traceSegment_057_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3577 34 = [0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3577 17 17, g32p_row03_traceSegment_057_3577_0017, g32p_row03_traceSegment_057_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3611 8 9, g32p_row03_traceSegment_057_3611_0008, g32p_row03_traceSegment_057_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3628 8 9, g32p_row03_traceSegment_057_3628_0008, g32p_row03_traceSegment_057_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3611 17 17, g32p_row03_traceSegment_057_3611_0017, g32p_row03_traceSegment_057_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 3577 68 = [0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3577 34 34, g32p_row03_traceSegment_057_3577_0034, g32p_row03_traceSegment_057_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 3510 135 = [0, 5, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3510 67 68, g32p_row03_traceSegment_057_3510_0067, g32p_row03_traceSegment_057_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3661 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3661 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3661 8 9, g32p_row03_traceSegment_057_3661_0008, g32p_row03_traceSegment_057_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 3645 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3645 16 17, g32p_row03_traceSegment_057_3645_0016, g32p_row03_traceSegment_057_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3678 8 9, g32p_row03_traceSegment_057_3678_0008, g32p_row03_traceSegment_057_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3703 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3695 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3695 8 9, g32p_row03_traceSegment_057_3695_0008, g32p_row03_traceSegment_057_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3678 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3678 17 17, g32p_row03_traceSegment_057_3678_0017, g32p_row03_traceSegment_057_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 3645 67 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3645 33 34, g32p_row03_traceSegment_057_3645_0033, g32p_row03_traceSegment_057_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3712 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3720 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3712 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3712 8 9, g32p_row03_traceSegment_057_3712_0008, g32p_row03_traceSegment_057_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3737 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3729 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3729 8 9, g32p_row03_traceSegment_057_3729_0008, g32p_row03_traceSegment_057_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3712 34 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3712 17 17, g32p_row03_traceSegment_057_3712_0017, g32p_row03_traceSegment_057_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3746 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3746 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3746 8 9, g32p_row03_traceSegment_057_3746_0008, g32p_row03_traceSegment_057_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3771 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3763 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3763 8 9, g32p_row03_traceSegment_057_3763_0008, g32p_row03_traceSegment_057_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3746 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3746 17 17, g32p_row03_traceSegment_057_3746_0017, g32p_row03_traceSegment_057_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 3712 68 = [0, 4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3712 34 34, g32p_row03_traceSegment_057_3712_0034, g32p_row03_traceSegment_057_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 3645 135 = [0, 6, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3645 67 68, g32p_row03_traceSegment_057_3645_0067, g32p_row03_traceSegment_057_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 3510 270 = [0, 11, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3510 135 135, g32p_row03_traceSegment_057_3510_0135, g32p_row03_traceSegment_057_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_057 3240 540 = [0, 16, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3240 270 270, g32p_row03_traceSegment_057_3240_0270, g32p_row03_traceSegment_057_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 3780 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3796 8 9, g32p_row03_traceSegment_057_3796_0008, g32p_row03_traceSegment_057_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 3780 33 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3780 16 17, g32p_row03_traceSegment_057_3780_0016, g32p_row03_traceSegment_057_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3821 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3813 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3813 8 9, g32p_row03_traceSegment_057_3813_0008, g32p_row03_traceSegment_057_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3830 8 9, g32p_row03_traceSegment_057_3830_0008, g32p_row03_traceSegment_057_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3813 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3813 17 17, g32p_row03_traceSegment_057_3813_0017, g32p_row03_traceSegment_057_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 3780 67 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3780 33 34, g32p_row03_traceSegment_057_3780_0033, g32p_row03_traceSegment_057_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3847 8 9, g32p_row03_traceSegment_057_3847_0008, g32p_row03_traceSegment_057_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3872 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3864 17 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3864 8 9, g32p_row03_traceSegment_057_3864_0008, g32p_row03_traceSegment_057_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3847 34 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3847 17 17, g32p_row03_traceSegment_057_3847_0017, g32p_row03_traceSegment_057_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3881 8 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3881 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3881 8 9, g32p_row03_traceSegment_057_3881_0008, g32p_row03_traceSegment_057_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3898 8 9, g32p_row03_traceSegment_057_3898_0008, g32p_row03_traceSegment_057_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3881 34 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3881 17 17, g32p_row03_traceSegment_057_3881_0017, g32p_row03_traceSegment_057_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 3847 68 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3847 34 34, g32p_row03_traceSegment_057_3847_0034, g32p_row03_traceSegment_057_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 3780 135 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3780 67 68, g32p_row03_traceSegment_057_3780_0067, g32p_row03_traceSegment_057_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 3915 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3939 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3931 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3931 8 9, g32p_row03_traceSegment_057_3931_0008, g32p_row03_traceSegment_057_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 3915 33 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3915 16 17, g32p_row03_traceSegment_057_3915_0016, g32p_row03_traceSegment_057_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3948 8 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3956 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3948 17 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3948 8 9, g32p_row03_traceSegment_057_3948_0008, g32p_row03_traceSegment_057_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3965 8 9, g32p_row03_traceSegment_057_3965_0008, g32p_row03_traceSegment_057_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3948 34 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3948 17 17, g32p_row03_traceSegment_057_3948_0017, g32p_row03_traceSegment_057_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 3915 67 = [0, 1, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3915 33 34, g32p_row03_traceSegment_057_3915_0033, g32p_row03_traceSegment_057_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3982 8 9, g32p_row03_traceSegment_057_3982_0008, g32p_row03_traceSegment_057_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3999 8 9, g32p_row03_traceSegment_057_3999_0008, g32p_row03_traceSegment_057_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3982 17 17, g32p_row03_traceSegment_057_3982_0017, g32p_row03_traceSegment_057_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4024 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4016 17 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4016 8 9, g32p_row03_traceSegment_057_4016_0008, g32p_row03_traceSegment_057_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4033 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4041 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4033 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4033 8 9, g32p_row03_traceSegment_057_4033_0008, g32p_row03_traceSegment_057_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 4016 34 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4016 17 17, g32p_row03_traceSegment_057_4016_0017, g32p_row03_traceSegment_057_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 3982 68 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3982 34 34, g32p_row03_traceSegment_057_3982_0034, g32p_row03_traceSegment_057_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 3915 135 = [0, 2, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3915 67 68, g32p_row03_traceSegment_057_3915_0067, g32p_row03_traceSegment_057_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 3780 270 = [0, 7, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3780 135 135, g32p_row03_traceSegment_057_3780_0135, g32p_row03_traceSegment_057_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 4050 16 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4066 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4074 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4066 17 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4066 8 9, g32p_row03_traceSegment_057_4066_0008, g32p_row03_traceSegment_057_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 4050 33 = [0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4050 16 17, g32p_row03_traceSegment_057_4050_0016, g32p_row03_traceSegment_057_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4083 8 9, g32p_row03_traceSegment_057_4083_0008, g32p_row03_traceSegment_057_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4100 8 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4100 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4100 8 9, g32p_row03_traceSegment_057_4100_0008, g32p_row03_traceSegment_057_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 4083 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4083 17 17, g32p_row03_traceSegment_057_4083_0017, g32p_row03_traceSegment_057_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 4050 67 = [0, 1, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4050 33 34, g32p_row03_traceSegment_057_4050_0033, g32p_row03_traceSegment_057_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4117 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4125 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4117 17 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4117 8 9, g32p_row03_traceSegment_057_4117_0008, g32p_row03_traceSegment_057_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4134 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4142 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4134 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4134 8 9, g32p_row03_traceSegment_057_4134_0008, g32p_row03_traceSegment_057_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 4117 34 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4117 17 17, g32p_row03_traceSegment_057_4117_0017, g32p_row03_traceSegment_057_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4159 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4151 17 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4151 8 9, g32p_row03_traceSegment_057_4151_0008, g32p_row03_traceSegment_057_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4176 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4168 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4168 8 9, g32p_row03_traceSegment_057_4168_0008, g32p_row03_traceSegment_057_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 4151 34 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4151 17 17, g32p_row03_traceSegment_057_4151_0017, g32p_row03_traceSegment_057_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 4117 68 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4117 34 34, g32p_row03_traceSegment_057_4117_0034, g32p_row03_traceSegment_057_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 4050 135 = [0, 1, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4050 67 68, g32p_row03_traceSegment_057_4050_0067, g32p_row03_traceSegment_057_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_057 4185 16 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4201 8 9, g32p_row03_traceSegment_057_4201_0008, g32p_row03_traceSegment_057_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_057 4185 33 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4185 16 17, g32p_row03_traceSegment_057_4185_0016, g32p_row03_traceSegment_057_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4218 8 9, g32p_row03_traceSegment_057_4218_0008, g32p_row03_traceSegment_057_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4235 8 9, g32p_row03_traceSegment_057_4235_0008, g32p_row03_traceSegment_057_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4218 17 17, g32p_row03_traceSegment_057_4218_0017, g32p_row03_traceSegment_057_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_057 4185 67 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4185 33 34, g32p_row03_traceSegment_057_4185_0033, g32p_row03_traceSegment_057_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4252 8 9, g32p_row03_traceSegment_057_4252_0008, g32p_row03_traceSegment_057_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4269 8 9, g32p_row03_traceSegment_057_4269_0008, g32p_row03_traceSegment_057_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4252 17 17, g32p_row03_traceSegment_057_4252_0017, g32p_row03_traceSegment_057_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4286 8 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4286 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4286 8 9, g32p_row03_traceSegment_057_4286_0008, g32p_row03_traceSegment_057_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_057 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_057 4311 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_057_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_057 4303 17 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4303 8 9, g32p_row03_traceSegment_057_4303_0008, g32p_row03_traceSegment_057_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_057 4286 34 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4286 17 17, g32p_row03_traceSegment_057_4286_0017, g32p_row03_traceSegment_057_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_057 4252 68 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4252 34 34, g32p_row03_traceSegment_057_4252_0034, g32p_row03_traceSegment_057_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_057 4185 135 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4185 67 68, g32p_row03_traceSegment_057_4185_0067, g32p_row03_traceSegment_057_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_057_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_057 4050 270 = [0, 1, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 4050 135 135, g32p_row03_traceSegment_057_4050_0135, g32p_row03_traceSegment_057_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_057 3780 540 = [0, 8, 0, 0, 25] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3780 270 270, g32p_row03_traceSegment_057_3780_0270, g32p_row03_traceSegment_057_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_057_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_057 3240 1080 = [0, 24, 0, 0, 43] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 3240 540 540, g32p_row03_traceSegment_057_3240_0540, g32p_row03_traceSegment_057_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_057_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_057 2160 2160 = [0, 81, 0, 0, 76] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 2160 1080 1080, g32p_row03_traceSegment_057_2160_1080, g32p_row03_traceSegment_057_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_057_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_057 0 4320 = [0, 180, 0, 0, 180] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_057 0 2160 2160, g32p_row03_traceSegment_057_0000_2160, g32p_row03_traceSegment_057_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_057 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 57 = [0, 180, 0, 0, 180] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_057_0000_4320

end HodgeLean.Foundations.Program

end
end
