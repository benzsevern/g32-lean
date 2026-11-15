import HodgeLean.Foundations.Program.G32PropFourSixPacked0314
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_045 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 45 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_045_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 16 8 9, g32p_row03_traceSegment_045_0016_0008, g32p_row03_traceSegment_045_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 0 16 17, g32p_row03_traceSegment_045_0000_0016, g32p_row03_traceSegment_045_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 33 8 9, g32p_row03_traceSegment_045_0033_0008, g32p_row03_traceSegment_045_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 50 8 9, g32p_row03_traceSegment_045_0050_0008, g32p_row03_traceSegment_045_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 33 17 17, g32p_row03_traceSegment_045_0033_0017, g32p_row03_traceSegment_045_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 0 33 34, g32p_row03_traceSegment_045_0000_0033, g32p_row03_traceSegment_045_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 67 8 9, g32p_row03_traceSegment_045_0067_0008, g32p_row03_traceSegment_045_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 84 8 9, g32p_row03_traceSegment_045_0084_0008, g32p_row03_traceSegment_045_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 67 17 17, g32p_row03_traceSegment_045_0067_0017, g32p_row03_traceSegment_045_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 101 8 9, g32p_row03_traceSegment_045_0101_0008, g32p_row03_traceSegment_045_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 118 8 9, g32p_row03_traceSegment_045_0118_0008, g32p_row03_traceSegment_045_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 101 17 17, g32p_row03_traceSegment_045_0101_0017, g32p_row03_traceSegment_045_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 67 34 34, g32p_row03_traceSegment_045_0067_0034, g32p_row03_traceSegment_045_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 0 67 68, g32p_row03_traceSegment_045_0000_0067, g32p_row03_traceSegment_045_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 135 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 151 8 9, g32p_row03_traceSegment_045_0151_0008, g32p_row03_traceSegment_045_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 135 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 135 16 17, g32p_row03_traceSegment_045_0135_0016, g32p_row03_traceSegment_045_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 168 8 9, g32p_row03_traceSegment_045_0168_0008, g32p_row03_traceSegment_045_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 185 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 193 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 185 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 185 8 9, g32p_row03_traceSegment_045_0185_0008, g32p_row03_traceSegment_045_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 168 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 168 17 17, g32p_row03_traceSegment_045_0168_0017, g32p_row03_traceSegment_045_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 135 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 135 33 34, g32p_row03_traceSegment_045_0135_0033, g32p_row03_traceSegment_045_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 202 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 202 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 202 8 9, g32p_row03_traceSegment_045_0202_0008, g32p_row03_traceSegment_045_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 219 8 9, g32p_row03_traceSegment_045_0219_0008, g32p_row03_traceSegment_045_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 202 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 202 17 17, g32p_row03_traceSegment_045_0202_0017, g32p_row03_traceSegment_045_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 236 8 9, g32p_row03_traceSegment_045_0236_0008, g32p_row03_traceSegment_045_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 253 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 261 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 253 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 253 8 9, g32p_row03_traceSegment_045_0253_0008, g32p_row03_traceSegment_045_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 236 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 236 17 17, g32p_row03_traceSegment_045_0236_0017, g32p_row03_traceSegment_045_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 202 68 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 202 34 34, g32p_row03_traceSegment_045_0202_0034, g32p_row03_traceSegment_045_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 135 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 135 67 68, g32p_row03_traceSegment_045_0135_0067, g32p_row03_traceSegment_045_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 0 270 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 0 135 135, g32p_row03_traceSegment_045_0000_0135, g32p_row03_traceSegment_045_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 270 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 286 8 9, g32p_row03_traceSegment_045_0286_0008, g32p_row03_traceSegment_045_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 270 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 270 16 17, g32p_row03_traceSegment_045_0270_0016, g32p_row03_traceSegment_045_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 311 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 303 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 303 8 9, g32p_row03_traceSegment_045_0303_0008, g32p_row03_traceSegment_045_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 328 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 320 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 320 8 9, g32p_row03_traceSegment_045_0320_0008, g32p_row03_traceSegment_045_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 303 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 303 17 17, g32p_row03_traceSegment_045_0303_0017, g32p_row03_traceSegment_045_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 270 67 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 270 33 34, g32p_row03_traceSegment_045_0270_0033, g32p_row03_traceSegment_045_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 337 8 9, g32p_row03_traceSegment_045_0337_0008, g32p_row03_traceSegment_045_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 354 8 9, g32p_row03_traceSegment_045_0354_0008, g32p_row03_traceSegment_045_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 337 17 17, g32p_row03_traceSegment_045_0337_0017, g32p_row03_traceSegment_045_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 371 8 9, g32p_row03_traceSegment_045_0371_0008, g32p_row03_traceSegment_045_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 388 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 388 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 388 8 9, g32p_row03_traceSegment_045_0388_0008, g32p_row03_traceSegment_045_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 371 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 371 17 17, g32p_row03_traceSegment_045_0371_0017, g32p_row03_traceSegment_045_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 337 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 337 34 34, g32p_row03_traceSegment_045_0337_0034, g32p_row03_traceSegment_045_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 270 135 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 270 67 68, g32p_row03_traceSegment_045_0270_0067, g32p_row03_traceSegment_045_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 421 8 9, g32p_row03_traceSegment_045_0421_0008, g32p_row03_traceSegment_045_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 405 16 17, g32p_row03_traceSegment_045_0405_0016, g32p_row03_traceSegment_045_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 446 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 438 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 438 8 9, g32p_row03_traceSegment_045_0438_0008, g32p_row03_traceSegment_045_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 463 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 455 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 455 8 9, g32p_row03_traceSegment_045_0455_0008, g32p_row03_traceSegment_045_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 438 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 438 17 17, g32p_row03_traceSegment_045_0438_0017, g32p_row03_traceSegment_045_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 405 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 405 33 34, g32p_row03_traceSegment_045_0405_0033, g32p_row03_traceSegment_045_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 472 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 480 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 472 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 472 8 9, g32p_row03_traceSegment_045_0472_0008, g32p_row03_traceSegment_045_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 489 8 9, g32p_row03_traceSegment_045_0489_0008, g32p_row03_traceSegment_045_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 472 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 472 17 17, g32p_row03_traceSegment_045_0472_0017, g32p_row03_traceSegment_045_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 506 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 506 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 506 8 9, g32p_row03_traceSegment_045_0506_0008, g32p_row03_traceSegment_045_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 523 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 523 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 523 8 9, g32p_row03_traceSegment_045_0523_0008, g32p_row03_traceSegment_045_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 506 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 506 17 17, g32p_row03_traceSegment_045_0506_0017, g32p_row03_traceSegment_045_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 472 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 472 34 34, g32p_row03_traceSegment_045_0472_0034, g32p_row03_traceSegment_045_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 405 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 405 67 68, g32p_row03_traceSegment_045_0405_0067, g32p_row03_traceSegment_045_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 270 270 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 270 135 135, g32p_row03_traceSegment_045_0270_0135, g32p_row03_traceSegment_045_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_045 0 540 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 0 270 270, g32p_row03_traceSegment_045_0000_0270, g32p_row03_traceSegment_045_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 540 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 556 8 9, g32p_row03_traceSegment_045_0556_0008, g32p_row03_traceSegment_045_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 540 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 540 16 17, g32p_row03_traceSegment_045_0540_0016, g32p_row03_traceSegment_045_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 581 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 573 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 573 8 9, g32p_row03_traceSegment_045_0573_0008, g32p_row03_traceSegment_045_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 590 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 598 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 590 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 590 8 9, g32p_row03_traceSegment_045_0590_0008, g32p_row03_traceSegment_045_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 573 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 573 17 17, g32p_row03_traceSegment_045_0573_0017, g32p_row03_traceSegment_045_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 540 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 540 33 34, g32p_row03_traceSegment_045_0540_0033, g32p_row03_traceSegment_045_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 615 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 607 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 607 8 9, g32p_row03_traceSegment_045_0607_0008, g32p_row03_traceSegment_045_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 624 8 9, g32p_row03_traceSegment_045_0624_0008, g32p_row03_traceSegment_045_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 607 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 607 17 17, g32p_row03_traceSegment_045_0607_0017, g32p_row03_traceSegment_045_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 641 8 9, g32p_row03_traceSegment_045_0641_0008, g32p_row03_traceSegment_045_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 658 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 666 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 658 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 658 8 9, g32p_row03_traceSegment_045_0658_0008, g32p_row03_traceSegment_045_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 641 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 641 17 17, g32p_row03_traceSegment_045_0641_0017, g32p_row03_traceSegment_045_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 607 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 607 34 34, g32p_row03_traceSegment_045_0607_0034, g32p_row03_traceSegment_045_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 540 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 540 67 68, g32p_row03_traceSegment_045_0540_0067, g32p_row03_traceSegment_045_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 691 8 9, g32p_row03_traceSegment_045_0691_0008, g32p_row03_traceSegment_045_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 675 16 17, g32p_row03_traceSegment_045_0675_0016, g32p_row03_traceSegment_045_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 708 8 9, g32p_row03_traceSegment_045_0708_0008, g32p_row03_traceSegment_045_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 733 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 725 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 725 8 9, g32p_row03_traceSegment_045_0725_0008, g32p_row03_traceSegment_045_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 708 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 708 17 17, g32p_row03_traceSegment_045_0708_0017, g32p_row03_traceSegment_045_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 675 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 675 33 34, g32p_row03_traceSegment_045_0675_0033, g32p_row03_traceSegment_045_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 742 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 750 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 742 17 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 742 8 9, g32p_row03_traceSegment_045_0742_0008, g32p_row03_traceSegment_045_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 759 8 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 759 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 759 8 9, g32p_row03_traceSegment_045_0759_0008, g32p_row03_traceSegment_045_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 742 34 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 742 17 17, g32p_row03_traceSegment_045_0742_0017, g32p_row03_traceSegment_045_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 776 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 784 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 776 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 776 8 9, g32p_row03_traceSegment_045_0776_0008, g32p_row03_traceSegment_045_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 793 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 801 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 793 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 793 8 9, g32p_row03_traceSegment_045_0793_0008, g32p_row03_traceSegment_045_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 776 34 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 776 17 17, g32p_row03_traceSegment_045_0776_0017, g32p_row03_traceSegment_045_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 742 68 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 742 34 34, g32p_row03_traceSegment_045_0742_0034, g32p_row03_traceSegment_045_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 675 135 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 675 67 68, g32p_row03_traceSegment_045_0675_0067, g32p_row03_traceSegment_045_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 540 270 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 540 135 135, g32p_row03_traceSegment_045_0540_0135, g32p_row03_traceSegment_045_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 826 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 834 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 826 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 826 8 9, g32p_row03_traceSegment_045_0826_0008, g32p_row03_traceSegment_045_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 810 33 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 810 16 17, g32p_row03_traceSegment_045_0810_0016, g32p_row03_traceSegment_045_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 843 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 851 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 843 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 843 8 9, g32p_row03_traceSegment_045_0843_0008, g32p_row03_traceSegment_045_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 868 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 860 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 860 8 9, g32p_row03_traceSegment_045_0860_0008, g32p_row03_traceSegment_045_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 843 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 843 17 17, g32p_row03_traceSegment_045_0843_0017, g32p_row03_traceSegment_045_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 810 67 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 810 33 34, g32p_row03_traceSegment_045_0810_0033, g32p_row03_traceSegment_045_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 877 8 9, g32p_row03_traceSegment_045_0877_0008, g32p_row03_traceSegment_045_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 894 8 9, g32p_row03_traceSegment_045_0894_0008, g32p_row03_traceSegment_045_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 877 17 17, g32p_row03_traceSegment_045_0877_0017, g32p_row03_traceSegment_045_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 911 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 911 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 911 8 9, g32p_row03_traceSegment_045_0911_0008, g32p_row03_traceSegment_045_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 928 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 936 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 928 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 928 8 9, g32p_row03_traceSegment_045_0928_0008, g32p_row03_traceSegment_045_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 911 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 911 17 17, g32p_row03_traceSegment_045_0911_0017, g32p_row03_traceSegment_045_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 877 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 877 34 34, g32p_row03_traceSegment_045_0877_0034, g32p_row03_traceSegment_045_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 810 135 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 810 67 68, g32p_row03_traceSegment_045_0810_0067, g32p_row03_traceSegment_045_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 969 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 961 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 961 8 9, g32p_row03_traceSegment_045_0961_0008, g32p_row03_traceSegment_045_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 945 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 945 16 17, g32p_row03_traceSegment_045_0945_0016, g32p_row03_traceSegment_045_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 978 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 978 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 978 8 9, g32p_row03_traceSegment_045_0978_0008, g32p_row03_traceSegment_045_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 995 8 9, g32p_row03_traceSegment_045_0995_0008, g32p_row03_traceSegment_045_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 978 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 978 17 17, g32p_row03_traceSegment_045_0978_0017, g32p_row03_traceSegment_045_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 945 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 945 33 34, g32p_row03_traceSegment_045_0945_0033, g32p_row03_traceSegment_045_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1012 8 9, g32p_row03_traceSegment_045_1012_0008, g32p_row03_traceSegment_045_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1029 8 9, g32p_row03_traceSegment_045_1029_0008, g32p_row03_traceSegment_045_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1012 17 17, g32p_row03_traceSegment_045_1012_0017, g32p_row03_traceSegment_045_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1046 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1046 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1046 8 9, g32p_row03_traceSegment_045_1046_0008, g32p_row03_traceSegment_045_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1063 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1063 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1063 8 9, g32p_row03_traceSegment_045_1063_0008, g32p_row03_traceSegment_045_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1046 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1046 17 17, g32p_row03_traceSegment_045_1046_0017, g32p_row03_traceSegment_045_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 1012 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1012 34 34, g32p_row03_traceSegment_045_1012_0034, g32p_row03_traceSegment_045_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 945 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 945 67 68, g32p_row03_traceSegment_045_0945_0067, g32p_row03_traceSegment_045_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 810 270 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 810 135 135, g32p_row03_traceSegment_045_0810_0135, g32p_row03_traceSegment_045_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_045 540 540 = [0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 540 270 270, g32p_row03_traceSegment_045_0540_0270, g32p_row03_traceSegment_045_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_045 0 1080 = [0, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 0 540 540, g32p_row03_traceSegment_045_0000_0540, g32p_row03_traceSegment_045_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 1080 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1096 8 9, g32p_row03_traceSegment_045_1096_0008, g32p_row03_traceSegment_045_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 1080 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1080 16 17, g32p_row03_traceSegment_045_1080_0016, g32p_row03_traceSegment_045_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1113 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1121 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1113 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1113 8 9, g32p_row03_traceSegment_045_1113_0008, g32p_row03_traceSegment_045_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1130 8 9, g32p_row03_traceSegment_045_1130_0008, g32p_row03_traceSegment_045_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1113 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1113 17 17, g32p_row03_traceSegment_045_1113_0017, g32p_row03_traceSegment_045_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 1080 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1080 33 34, g32p_row03_traceSegment_045_1080_0033, g32p_row03_traceSegment_045_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1155 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1147 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1147 8 9, g32p_row03_traceSegment_045_1147_0008, g32p_row03_traceSegment_045_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1164 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1172 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1164 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1164 8 9, g32p_row03_traceSegment_045_1164_0008, g32p_row03_traceSegment_045_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1147 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1147 17 17, g32p_row03_traceSegment_045_1147_0017, g32p_row03_traceSegment_045_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1189 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1181 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1181 8 9, g32p_row03_traceSegment_045_1181_0008, g32p_row03_traceSegment_045_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1198 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1198 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1198 8 9, g32p_row03_traceSegment_045_1198_0008, g32p_row03_traceSegment_045_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1181 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1181 17 17, g32p_row03_traceSegment_045_1181_0017, g32p_row03_traceSegment_045_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 1147 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1147 34 34, g32p_row03_traceSegment_045_1147_0034, g32p_row03_traceSegment_045_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 1080 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1080 67 68, g32p_row03_traceSegment_045_1080_0067, g32p_row03_traceSegment_045_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 1215 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1231 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1231 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1231 8 9, g32p_row03_traceSegment_045_1231_0008, g32p_row03_traceSegment_045_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 1215 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1215 16 17, g32p_row03_traceSegment_045_1215_0016, g32p_row03_traceSegment_045_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1248 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1248 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1248 8 9, g32p_row03_traceSegment_045_1248_0008, g32p_row03_traceSegment_045_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1265 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1273 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1265 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1265 8 9, g32p_row03_traceSegment_045_1265_0008, g32p_row03_traceSegment_045_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1248 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1248 17 17, g32p_row03_traceSegment_045_1248_0017, g32p_row03_traceSegment_045_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 1215 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1215 33 34, g32p_row03_traceSegment_045_1215_0033, g32p_row03_traceSegment_045_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1282 8 9, g32p_row03_traceSegment_045_1282_0008, g32p_row03_traceSegment_045_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1299 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1307 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1299 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1299 8 9, g32p_row03_traceSegment_045_1299_0008, g32p_row03_traceSegment_045_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1282 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1282 17 17, g32p_row03_traceSegment_045_1282_0017, g32p_row03_traceSegment_045_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1316 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1324 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1316 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1316 8 9, g32p_row03_traceSegment_045_1316_0008, g32p_row03_traceSegment_045_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1333 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1341 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1333 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1333 8 9, g32p_row03_traceSegment_045_1333_0008, g32p_row03_traceSegment_045_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1316 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1316 17 17, g32p_row03_traceSegment_045_1316_0017, g32p_row03_traceSegment_045_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 1282 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1282 34 34, g32p_row03_traceSegment_045_1282_0034, g32p_row03_traceSegment_045_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 1215 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1215 67 68, g32p_row03_traceSegment_045_1215_0067, g32p_row03_traceSegment_045_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 1080 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1080 135 135, g32p_row03_traceSegment_045_1080_0135, g32p_row03_traceSegment_045_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 1350 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1374 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1366 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1366 8 9, g32p_row03_traceSegment_045_1366_0008, g32p_row03_traceSegment_045_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 1350 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1350 16 17, g32p_row03_traceSegment_045_1350_0016, g32p_row03_traceSegment_045_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1391 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1383 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1383 8 9, g32p_row03_traceSegment_045_1383_0008, g32p_row03_traceSegment_045_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1400 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1400 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1400 8 9, g32p_row03_traceSegment_045_1400_0008, g32p_row03_traceSegment_045_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1383 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1383 17 17, g32p_row03_traceSegment_045_1383_0017, g32p_row03_traceSegment_045_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 1350 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1350 33 34, g32p_row03_traceSegment_045_1350_0033, g32p_row03_traceSegment_045_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1417 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1417 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1417 8 9, g32p_row03_traceSegment_045_1417_0008, g32p_row03_traceSegment_045_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1434 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1442 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1434 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1434 8 9, g32p_row03_traceSegment_045_1434_0008, g32p_row03_traceSegment_045_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1417 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1417 17 17, g32p_row03_traceSegment_045_1417_0017, g32p_row03_traceSegment_045_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1451 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1451 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1451 8 9, g32p_row03_traceSegment_045_1451_0008, g32p_row03_traceSegment_045_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1468 8 9, g32p_row03_traceSegment_045_1468_0008, g32p_row03_traceSegment_045_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1451 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1451 17 17, g32p_row03_traceSegment_045_1451_0017, g32p_row03_traceSegment_045_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 1417 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1417 34 34, g32p_row03_traceSegment_045_1417_0034, g32p_row03_traceSegment_045_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 1350 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1350 67 68, g32p_row03_traceSegment_045_1350_0067, g32p_row03_traceSegment_045_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 1485 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1501 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1501 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1501 8 9, g32p_row03_traceSegment_045_1501_0008, g32p_row03_traceSegment_045_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 1485 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1485 16 17, g32p_row03_traceSegment_045_1485_0016, g32p_row03_traceSegment_045_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1526 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1518 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1518 8 9, g32p_row03_traceSegment_045_1518_0008, g32p_row03_traceSegment_045_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1543 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1535 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1535 8 9, g32p_row03_traceSegment_045_1535_0008, g32p_row03_traceSegment_045_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1518 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1518 17 17, g32p_row03_traceSegment_045_1518_0017, g32p_row03_traceSegment_045_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 1485 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1485 33 34, g32p_row03_traceSegment_045_1485_0033, g32p_row03_traceSegment_045_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1552 8 9, g32p_row03_traceSegment_045_1552_0008, g32p_row03_traceSegment_045_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1569 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1569 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1569 8 9, g32p_row03_traceSegment_045_1569_0008, g32p_row03_traceSegment_045_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1552 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1552 17 17, g32p_row03_traceSegment_045_1552_0017, g32p_row03_traceSegment_045_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1594 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1586 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1586 8 9, g32p_row03_traceSegment_045_1586_0008, g32p_row03_traceSegment_045_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1603 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1603 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1603 8 9, g32p_row03_traceSegment_045_1603_0008, g32p_row03_traceSegment_045_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1586 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1586 17 17, g32p_row03_traceSegment_045_1586_0017, g32p_row03_traceSegment_045_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 1552 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1552 34 34, g32p_row03_traceSegment_045_1552_0034, g32p_row03_traceSegment_045_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 1485 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1485 67 68, g32p_row03_traceSegment_045_1485_0067, g32p_row03_traceSegment_045_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 1350 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1350 135 135, g32p_row03_traceSegment_045_1350_0135, g32p_row03_traceSegment_045_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_045 1080 540 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1080 270 270, g32p_row03_traceSegment_045_1080_0270, g32p_row03_traceSegment_045_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 1620 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1636 8 9, g32p_row03_traceSegment_045_1636_0008, g32p_row03_traceSegment_045_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 1620 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1620 16 17, g32p_row03_traceSegment_045_1620_0016, g32p_row03_traceSegment_045_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1653 8 9, g32p_row03_traceSegment_045_1653_0008, g32p_row03_traceSegment_045_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1678 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1670 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1670 8 9, g32p_row03_traceSegment_045_1670_0008, g32p_row03_traceSegment_045_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1653 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1653 17 17, g32p_row03_traceSegment_045_1653_0017, g32p_row03_traceSegment_045_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 1620 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1620 33 34, g32p_row03_traceSegment_045_1620_0033, g32p_row03_traceSegment_045_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1687 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1695 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1687 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1687 8 9, g32p_row03_traceSegment_045_1687_0008, g32p_row03_traceSegment_045_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1712 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1704 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1704 8 9, g32p_row03_traceSegment_045_1704_0008, g32p_row03_traceSegment_045_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1687 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1687 17 17, g32p_row03_traceSegment_045_1687_0017, g32p_row03_traceSegment_045_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1729 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1721 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1721 8 9, g32p_row03_traceSegment_045_1721_0008, g32p_row03_traceSegment_045_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1738 8 9, g32p_row03_traceSegment_045_1738_0008, g32p_row03_traceSegment_045_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1721 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1721 17 17, g32p_row03_traceSegment_045_1721_0017, g32p_row03_traceSegment_045_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 1687 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1687 34 34, g32p_row03_traceSegment_045_1687_0034, g32p_row03_traceSegment_045_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 1620 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1620 67 68, g32p_row03_traceSegment_045_1620_0067, g32p_row03_traceSegment_045_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 1755 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1771 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1771 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1771 8 9, g32p_row03_traceSegment_045_1771_0008, g32p_row03_traceSegment_045_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 1755 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1755 16 17, g32p_row03_traceSegment_045_1755_0016, g32p_row03_traceSegment_045_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1788 8 9, g32p_row03_traceSegment_045_1788_0008, g32p_row03_traceSegment_045_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1813 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1805 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1805 8 9, g32p_row03_traceSegment_045_1805_0008, g32p_row03_traceSegment_045_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1788 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1788 17 17, g32p_row03_traceSegment_045_1788_0017, g32p_row03_traceSegment_045_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 1755 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1755 33 34, g32p_row03_traceSegment_045_1755_0033, g32p_row03_traceSegment_045_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1822 8 9, g32p_row03_traceSegment_045_1822_0008, g32p_row03_traceSegment_045_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1839 8 9, g32p_row03_traceSegment_045_1839_0008, g32p_row03_traceSegment_045_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1822 17 17, g32p_row03_traceSegment_045_1822_0017, g32p_row03_traceSegment_045_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1864 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1856 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1856 8 9, g32p_row03_traceSegment_045_1856_0008, g32p_row03_traceSegment_045_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1881 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1873 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1873 8 9, g32p_row03_traceSegment_045_1873_0008, g32p_row03_traceSegment_045_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1856 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1856 17 17, g32p_row03_traceSegment_045_1856_0017, g32p_row03_traceSegment_045_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 1822 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1822 34 34, g32p_row03_traceSegment_045_1822_0034, g32p_row03_traceSegment_045_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 1755 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1755 67 68, g32p_row03_traceSegment_045_1755_0067, g32p_row03_traceSegment_045_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 1620 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1620 135 135, g32p_row03_traceSegment_045_1620_0135, g32p_row03_traceSegment_045_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1906 8 9, g32p_row03_traceSegment_045_1906_0008, g32p_row03_traceSegment_045_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1890 16 17, g32p_row03_traceSegment_045_1890_0016, g32p_row03_traceSegment_045_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1923 8 9, g32p_row03_traceSegment_045_1923_0008, g32p_row03_traceSegment_045_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1940 8 9, g32p_row03_traceSegment_045_1940_0008, g32p_row03_traceSegment_045_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1923 17 17, g32p_row03_traceSegment_045_1923_0017, g32p_row03_traceSegment_045_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1890 33 34, g32p_row03_traceSegment_045_1890_0033, g32p_row03_traceSegment_045_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1957 8 9, g32p_row03_traceSegment_045_1957_0008, g32p_row03_traceSegment_045_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1974 8 9, g32p_row03_traceSegment_045_1974_0008, g32p_row03_traceSegment_045_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1957 17 17, g32p_row03_traceSegment_045_1957_0017, g32p_row03_traceSegment_045_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 1999 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 1991 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1991 8 9, g32p_row03_traceSegment_045_1991_0008, g32p_row03_traceSegment_045_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2008 8 9, g32p_row03_traceSegment_045_2008_0008, g32p_row03_traceSegment_045_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 1991 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1991 17 17, g32p_row03_traceSegment_045_1991_0017, g32p_row03_traceSegment_045_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 1957 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1957 34 34, g32p_row03_traceSegment_045_1957_0034, g32p_row03_traceSegment_045_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 1890 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1890 67 68, g32p_row03_traceSegment_045_1890_0067, g32p_row03_traceSegment_045_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2041 8 9, g32p_row03_traceSegment_045_2041_0008, g32p_row03_traceSegment_045_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2025 16 17, g32p_row03_traceSegment_045_2025_0016, g32p_row03_traceSegment_045_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2058 8 9, g32p_row03_traceSegment_045_2058_0008, g32p_row03_traceSegment_045_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2075 8 9, g32p_row03_traceSegment_045_2075_0008, g32p_row03_traceSegment_045_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2058 17 17, g32p_row03_traceSegment_045_2058_0017, g32p_row03_traceSegment_045_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2025 33 34, g32p_row03_traceSegment_045_2025_0033, g32p_row03_traceSegment_045_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2092 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2092 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2092 8 9, g32p_row03_traceSegment_045_2092_0008, g32p_row03_traceSegment_045_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2109 8 9, g32p_row03_traceSegment_045_2109_0008, g32p_row03_traceSegment_045_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2092 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2092 17 17, g32p_row03_traceSegment_045_2092_0017, g32p_row03_traceSegment_045_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2126 8 9, g32p_row03_traceSegment_045_2126_0008, g32p_row03_traceSegment_045_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2143 8 9, g32p_row03_traceSegment_045_2143_0008, g32p_row03_traceSegment_045_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2126 17 17, g32p_row03_traceSegment_045_2126_0017, g32p_row03_traceSegment_045_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 2092 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2092 34 34, g32p_row03_traceSegment_045_2092_0034, g32p_row03_traceSegment_045_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 2025 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2025 67 68, g32p_row03_traceSegment_045_2025_0067, g32p_row03_traceSegment_045_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 1890 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1890 135 135, g32p_row03_traceSegment_045_1890_0135, g32p_row03_traceSegment_045_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_045 1620 540 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1620 270 270, g32p_row03_traceSegment_045_1620_0270, g32p_row03_traceSegment_045_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_045_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_045 1080 1080 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 1080 540 540, g32p_row03_traceSegment_045_1080_0540, g32p_row03_traceSegment_045_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_045 0 2160 = [0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 0 1080 1080, g32p_row03_traceSegment_045_0000_1080, g32p_row03_traceSegment_045_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 2160 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2176 8 9, g32p_row03_traceSegment_045_2176_0008, g32p_row03_traceSegment_045_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 2160 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2160 16 17, g32p_row03_traceSegment_045_2160_0016, g32p_row03_traceSegment_045_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2193 8 9, g32p_row03_traceSegment_045_2193_0008, g32p_row03_traceSegment_045_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2210 8 9, g32p_row03_traceSegment_045_2210_0008, g32p_row03_traceSegment_045_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2193 17 17, g32p_row03_traceSegment_045_2193_0017, g32p_row03_traceSegment_045_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 2160 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2160 33 34, g32p_row03_traceSegment_045_2160_0033, g32p_row03_traceSegment_045_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2235 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2227 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2227 8 9, g32p_row03_traceSegment_045_2227_0008, g32p_row03_traceSegment_045_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2244 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2252 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2244 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2244 8 9, g32p_row03_traceSegment_045_2244_0008, g32p_row03_traceSegment_045_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2227 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2227 17 17, g32p_row03_traceSegment_045_2227_0017, g32p_row03_traceSegment_045_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2261 8 9, g32p_row03_traceSegment_045_2261_0008, g32p_row03_traceSegment_045_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2286 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2278 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2278 8 9, g32p_row03_traceSegment_045_2278_0008, g32p_row03_traceSegment_045_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2261 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2261 17 17, g32p_row03_traceSegment_045_2261_0017, g32p_row03_traceSegment_045_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 2227 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2227 34 34, g32p_row03_traceSegment_045_2227_0034, g32p_row03_traceSegment_045_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 2160 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2160 67 68, g32p_row03_traceSegment_045_2160_0067, g32p_row03_traceSegment_045_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 2295 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2319 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2311 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2311 8 9, g32p_row03_traceSegment_045_2311_0008, g32p_row03_traceSegment_045_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 2295 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2295 16 17, g32p_row03_traceSegment_045_2295_0016, g32p_row03_traceSegment_045_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2328 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2328 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2328 8 9, g32p_row03_traceSegment_045_2328_0008, g32p_row03_traceSegment_045_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2345 8 9, g32p_row03_traceSegment_045_2345_0008, g32p_row03_traceSegment_045_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2328 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2328 17 17, g32p_row03_traceSegment_045_2328_0017, g32p_row03_traceSegment_045_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 2295 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2295 33 34, g32p_row03_traceSegment_045_2295_0033, g32p_row03_traceSegment_045_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2362 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2362 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2362 8 9, g32p_row03_traceSegment_045_2362_0008, g32p_row03_traceSegment_045_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2379 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2379 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2379 8 9, g32p_row03_traceSegment_045_2379_0008, g32p_row03_traceSegment_045_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2362 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2362 17 17, g32p_row03_traceSegment_045_2362_0017, g32p_row03_traceSegment_045_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2396 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2396 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2396 8 9, g32p_row03_traceSegment_045_2396_0008, g32p_row03_traceSegment_045_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2413 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2421 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2413 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2413 8 9, g32p_row03_traceSegment_045_2413_0008, g32p_row03_traceSegment_045_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2396 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2396 17 17, g32p_row03_traceSegment_045_2396_0017, g32p_row03_traceSegment_045_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 2362 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2362 34 34, g32p_row03_traceSegment_045_2362_0034, g32p_row03_traceSegment_045_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 2295 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2295 67 68, g32p_row03_traceSegment_045_2295_0067, g32p_row03_traceSegment_045_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 2160 270 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2160 135 135, g32p_row03_traceSegment_045_2160_0135, g32p_row03_traceSegment_045_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 2430 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2446 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2454 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2446 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2446 8 9, g32p_row03_traceSegment_045_2446_0008, g32p_row03_traceSegment_045_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 2430 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2430 16 17, g32p_row03_traceSegment_045_2430_0016, g32p_row03_traceSegment_045_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2463 8 9, g32p_row03_traceSegment_045_2463_0008, g32p_row03_traceSegment_045_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2480 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2488 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2480 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2480 8 9, g32p_row03_traceSegment_045_2480_0008, g32p_row03_traceSegment_045_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2463 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2463 17 17, g32p_row03_traceSegment_045_2463_0017, g32p_row03_traceSegment_045_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 2430 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2430 33 34, g32p_row03_traceSegment_045_2430_0033, g32p_row03_traceSegment_045_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2497 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2497 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2497 8 9, g32p_row03_traceSegment_045_2497_0008, g32p_row03_traceSegment_045_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2514 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2522 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2514 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2514 8 9, g32p_row03_traceSegment_045_2514_0008, g32p_row03_traceSegment_045_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2497 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2497 17 17, g32p_row03_traceSegment_045_2497_0017, g32p_row03_traceSegment_045_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2531 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2531 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2531 8 9, g32p_row03_traceSegment_045_2531_0008, g32p_row03_traceSegment_045_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2548 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2556 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2548 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2548 8 9, g32p_row03_traceSegment_045_2548_0008, g32p_row03_traceSegment_045_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2531 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2531 17 17, g32p_row03_traceSegment_045_2531_0017, g32p_row03_traceSegment_045_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 2497 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2497 34 34, g32p_row03_traceSegment_045_2497_0034, g32p_row03_traceSegment_045_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 2430 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2430 67 68, g32p_row03_traceSegment_045_2430_0067, g32p_row03_traceSegment_045_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 2565 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2581 8 9, g32p_row03_traceSegment_045_2581_0008, g32p_row03_traceSegment_045_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 2565 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2565 16 17, g32p_row03_traceSegment_045_2565_0016, g32p_row03_traceSegment_045_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2598 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2598 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2598 8 9, g32p_row03_traceSegment_045_2598_0008, g32p_row03_traceSegment_045_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2623 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2615 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2615 8 9, g32p_row03_traceSegment_045_2615_0008, g32p_row03_traceSegment_045_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2598 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2598 17 17, g32p_row03_traceSegment_045_2598_0017, g32p_row03_traceSegment_045_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 2565 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2565 33 34, g32p_row03_traceSegment_045_2565_0033, g32p_row03_traceSegment_045_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2640 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2632 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2632 8 9, g32p_row03_traceSegment_045_2632_0008, g32p_row03_traceSegment_045_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2649 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2649 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2649 8 9, g32p_row03_traceSegment_045_2649_0008, g32p_row03_traceSegment_045_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2632 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2632 17 17, g32p_row03_traceSegment_045_2632_0017, g32p_row03_traceSegment_045_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2666 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2666 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2666 8 9, g32p_row03_traceSegment_045_2666_0008, g32p_row03_traceSegment_045_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2683 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2691 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2683 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2683 8 9, g32p_row03_traceSegment_045_2683_0008, g32p_row03_traceSegment_045_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2666 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2666 17 17, g32p_row03_traceSegment_045_2666_0017, g32p_row03_traceSegment_045_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 2632 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2632 34 34, g32p_row03_traceSegment_045_2632_0034, g32p_row03_traceSegment_045_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 2565 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2565 67 68, g32p_row03_traceSegment_045_2565_0067, g32p_row03_traceSegment_045_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 2430 270 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2430 135 135, g32p_row03_traceSegment_045_2430_0135, g32p_row03_traceSegment_045_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_045 2160 540 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2160 270 270, g32p_row03_traceSegment_045_2160_0270, g32p_row03_traceSegment_045_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 2700 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2716 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2724 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2716 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2716 8 9, g32p_row03_traceSegment_045_2716_0008, g32p_row03_traceSegment_045_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 2700 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2700 16 17, g32p_row03_traceSegment_045_2700_0016, g32p_row03_traceSegment_045_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2741 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2733 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2733 8 9, g32p_row03_traceSegment_045_2733_0008, g32p_row03_traceSegment_045_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2750 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2758 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2750 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2750 8 9, g32p_row03_traceSegment_045_2750_0008, g32p_row03_traceSegment_045_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2733 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2733 17 17, g32p_row03_traceSegment_045_2733_0017, g32p_row03_traceSegment_045_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 2700 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2700 33 34, g32p_row03_traceSegment_045_2700_0033, g32p_row03_traceSegment_045_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2767 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2775 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2767 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2767 8 9, g32p_row03_traceSegment_045_2767_0008, g32p_row03_traceSegment_045_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2784 8 9, g32p_row03_traceSegment_045_2784_0008, g32p_row03_traceSegment_045_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2767 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2767 17 17, g32p_row03_traceSegment_045_2767_0017, g32p_row03_traceSegment_045_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2801 8 9, g32p_row03_traceSegment_045_2801_0008, g32p_row03_traceSegment_045_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2818 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2826 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2818 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2818 8 9, g32p_row03_traceSegment_045_2818_0008, g32p_row03_traceSegment_045_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2801 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2801 17 17, g32p_row03_traceSegment_045_2801_0017, g32p_row03_traceSegment_045_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 2767 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2767 34 34, g32p_row03_traceSegment_045_2767_0034, g32p_row03_traceSegment_045_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 2700 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2700 67 68, g32p_row03_traceSegment_045_2700_0067, g32p_row03_traceSegment_045_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 2835 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2851 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2859 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2851 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2851 8 9, g32p_row03_traceSegment_045_2851_0008, g32p_row03_traceSegment_045_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 2835 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2835 16 17, g32p_row03_traceSegment_045_2835_0016, g32p_row03_traceSegment_045_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2868 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2876 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2868 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2868 8 9, g32p_row03_traceSegment_045_2868_0008, g32p_row03_traceSegment_045_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2885 8 9, g32p_row03_traceSegment_045_2885_0008, g32p_row03_traceSegment_045_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2868 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2868 17 17, g32p_row03_traceSegment_045_2868_0017, g32p_row03_traceSegment_045_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 2835 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2835 33 34, g32p_row03_traceSegment_045_2835_0033, g32p_row03_traceSegment_045_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2902 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2902 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2902 8 9, g32p_row03_traceSegment_045_2902_0008, g32p_row03_traceSegment_045_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2919 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2927 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2919 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2919 8 9, g32p_row03_traceSegment_045_2919_0008, g32p_row03_traceSegment_045_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2902 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2902 17 17, g32p_row03_traceSegment_045_2902_0017, g32p_row03_traceSegment_045_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2944 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2936 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2936 8 9, g32p_row03_traceSegment_045_2936_0008, g32p_row03_traceSegment_045_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2953 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2953 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2953 8 9, g32p_row03_traceSegment_045_2953_0008, g32p_row03_traceSegment_045_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 2936 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2936 17 17, g32p_row03_traceSegment_045_2936_0017, g32p_row03_traceSegment_045_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 2902 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2902 34 34, g32p_row03_traceSegment_045_2902_0034, g32p_row03_traceSegment_045_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 2835 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2835 67 68, g32p_row03_traceSegment_045_2835_0067, g32p_row03_traceSegment_045_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 2700 270 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2700 135 135, g32p_row03_traceSegment_045_2700_0135, g32p_row03_traceSegment_045_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 2970 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 2986 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 2986 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2986 8 9, g32p_row03_traceSegment_045_2986_0008, g32p_row03_traceSegment_045_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 2970 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2970 16 17, g32p_row03_traceSegment_045_2970_0016, g32p_row03_traceSegment_045_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3003 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3003 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3003 8 9, g32p_row03_traceSegment_045_3003_0008, g32p_row03_traceSegment_045_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3028 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3020 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3020 8 9, g32p_row03_traceSegment_045_3020_0008, g32p_row03_traceSegment_045_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3003 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3003 17 17, g32p_row03_traceSegment_045_3003_0017, g32p_row03_traceSegment_045_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 2970 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2970 33 34, g32p_row03_traceSegment_045_2970_0033, g32p_row03_traceSegment_045_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3037 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3045 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3037 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3037 8 9, g32p_row03_traceSegment_045_3037_0008, g32p_row03_traceSegment_045_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3054 8 9, g32p_row03_traceSegment_045_3054_0008, g32p_row03_traceSegment_045_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3037 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3037 17 17, g32p_row03_traceSegment_045_3037_0017, g32p_row03_traceSegment_045_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3071 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3071 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3071 8 9, g32p_row03_traceSegment_045_3071_0008, g32p_row03_traceSegment_045_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3088 8 9, g32p_row03_traceSegment_045_3088_0008, g32p_row03_traceSegment_045_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3071 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3071 17 17, g32p_row03_traceSegment_045_3071_0017, g32p_row03_traceSegment_045_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 3037 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3037 34 34, g32p_row03_traceSegment_045_3037_0034, g32p_row03_traceSegment_045_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 2970 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2970 67 68, g32p_row03_traceSegment_045_2970_0067, g32p_row03_traceSegment_045_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 3105 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3121 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3121 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3121 8 9, g32p_row03_traceSegment_045_3121_0008, g32p_row03_traceSegment_045_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 3105 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3105 16 17, g32p_row03_traceSegment_045_3105_0016, g32p_row03_traceSegment_045_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3146 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3138 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3138 8 9, g32p_row03_traceSegment_045_3138_0008, g32p_row03_traceSegment_045_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3155 8 9, g32p_row03_traceSegment_045_3155_0008, g32p_row03_traceSegment_045_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3138 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3138 17 17, g32p_row03_traceSegment_045_3138_0017, g32p_row03_traceSegment_045_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 3105 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3105 33 34, g32p_row03_traceSegment_045_3105_0033, g32p_row03_traceSegment_045_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3172 8 9, g32p_row03_traceSegment_045_3172_0008, g32p_row03_traceSegment_045_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3197 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3189 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3189 8 9, g32p_row03_traceSegment_045_3189_0008, g32p_row03_traceSegment_045_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3172 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3172 17 17, g32p_row03_traceSegment_045_3172_0017, g32p_row03_traceSegment_045_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3206 8 9, g32p_row03_traceSegment_045_3206_0008, g32p_row03_traceSegment_045_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3223 8 9, g32p_row03_traceSegment_045_3223_0008, g32p_row03_traceSegment_045_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3206 17 17, g32p_row03_traceSegment_045_3206_0017, g32p_row03_traceSegment_045_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 3172 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3172 34 34, g32p_row03_traceSegment_045_3172_0034, g32p_row03_traceSegment_045_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 3105 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3105 67 68, g32p_row03_traceSegment_045_3105_0067, g32p_row03_traceSegment_045_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 2970 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2970 135 135, g32p_row03_traceSegment_045_2970_0135, g32p_row03_traceSegment_045_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_045 2700 540 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2700 270 270, g32p_row03_traceSegment_045_2700_0270, g32p_row03_traceSegment_045_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_045 2160 1080 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2160 540 540, g32p_row03_traceSegment_045_2160_0540, g32p_row03_traceSegment_045_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3264 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3256 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3256 8 9, g32p_row03_traceSegment_045_3256_0008, g32p_row03_traceSegment_045_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 3240 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3240 16 17, g32p_row03_traceSegment_045_3240_0016, g32p_row03_traceSegment_045_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3273 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3273 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3273 8 9, g32p_row03_traceSegment_045_3273_0008, g32p_row03_traceSegment_045_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3290 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3290 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3290 8 9, g32p_row03_traceSegment_045_3290_0008, g32p_row03_traceSegment_045_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3273 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3273 17 17, g32p_row03_traceSegment_045_3273_0017, g32p_row03_traceSegment_045_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 3240 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3240 33 34, g32p_row03_traceSegment_045_3240_0033, g32p_row03_traceSegment_045_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3307 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3307 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3307 8 9, g32p_row03_traceSegment_045_3307_0008, g32p_row03_traceSegment_045_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3324 8 9, g32p_row03_traceSegment_045_3324_0008, g32p_row03_traceSegment_045_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3307 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3307 17 17, g32p_row03_traceSegment_045_3307_0017, g32p_row03_traceSegment_045_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3341 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3341 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3341 8 9, g32p_row03_traceSegment_045_3341_0008, g32p_row03_traceSegment_045_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3366 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3358 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3358 8 9, g32p_row03_traceSegment_045_3358_0008, g32p_row03_traceSegment_045_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3341 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3341 17 17, g32p_row03_traceSegment_045_3341_0017, g32p_row03_traceSegment_045_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 3307 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3307 34 34, g32p_row03_traceSegment_045_3307_0034, g32p_row03_traceSegment_045_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 3240 135 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3240 67 68, g32p_row03_traceSegment_045_3240_0067, g32p_row03_traceSegment_045_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3391 8 9, g32p_row03_traceSegment_045_3391_0008, g32p_row03_traceSegment_045_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3375 16 17, g32p_row03_traceSegment_045_3375_0016, g32p_row03_traceSegment_045_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3416 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3408 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3408 8 9, g32p_row03_traceSegment_045_3408_0008, g32p_row03_traceSegment_045_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3425 8 9, g32p_row03_traceSegment_045_3425_0008, g32p_row03_traceSegment_045_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3408 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3408 17 17, g32p_row03_traceSegment_045_3408_0017, g32p_row03_traceSegment_045_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 3375 67 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3375 33 34, g32p_row03_traceSegment_045_3375_0033, g32p_row03_traceSegment_045_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3442 8 9, g32p_row03_traceSegment_045_3442_0008, g32p_row03_traceSegment_045_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3459 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3459 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3459 8 9, g32p_row03_traceSegment_045_3459_0008, g32p_row03_traceSegment_045_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3442 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3442 17 17, g32p_row03_traceSegment_045_3442_0017, g32p_row03_traceSegment_045_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3476 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3476 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3476 8 9, g32p_row03_traceSegment_045_3476_0008, g32p_row03_traceSegment_045_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3493 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3493 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3493 8 9, g32p_row03_traceSegment_045_3493_0008, g32p_row03_traceSegment_045_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3476 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3476 17 17, g32p_row03_traceSegment_045_3476_0017, g32p_row03_traceSegment_045_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 3442 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3442 34 34, g32p_row03_traceSegment_045_3442_0034, g32p_row03_traceSegment_045_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 3375 135 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3375 67 68, g32p_row03_traceSegment_045_3375_0067, g32p_row03_traceSegment_045_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 3240 270 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3240 135 135, g32p_row03_traceSegment_045_3240_0135, g32p_row03_traceSegment_045_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 3510 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3526 8 9, g32p_row03_traceSegment_045_3526_0008, g32p_row03_traceSegment_045_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 3510 33 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3510 16 17, g32p_row03_traceSegment_045_3510_0016, g32p_row03_traceSegment_045_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3543 8 9, g32p_row03_traceSegment_045_3543_0008, g32p_row03_traceSegment_045_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3560 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3560 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3560 8 9, g32p_row03_traceSegment_045_3560_0008, g32p_row03_traceSegment_045_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3543 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3543 17 17, g32p_row03_traceSegment_045_3543_0017, g32p_row03_traceSegment_045_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 3510 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3510 33 34, g32p_row03_traceSegment_045_3510_0033, g32p_row03_traceSegment_045_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3577 8 9, g32p_row03_traceSegment_045_3577_0008, g32p_row03_traceSegment_045_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3594 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3594 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3594 8 9, g32p_row03_traceSegment_045_3594_0008, g32p_row03_traceSegment_045_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3577 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3577 17 17, g32p_row03_traceSegment_045_3577_0017, g32p_row03_traceSegment_045_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3611 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3619 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3611 17 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3611 8 9, g32p_row03_traceSegment_045_3611_0008, g32p_row03_traceSegment_045_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3628 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3628 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3628 8 9, g32p_row03_traceSegment_045_3628_0008, g32p_row03_traceSegment_045_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3611 34 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3611 17 17, g32p_row03_traceSegment_045_3611_0017, g32p_row03_traceSegment_045_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 3577 68 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3577 34 34, g32p_row03_traceSegment_045_3577_0034, g32p_row03_traceSegment_045_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 3510 135 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3510 67 68, g32p_row03_traceSegment_045_3510_0067, g32p_row03_traceSegment_045_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3661 8 9, g32p_row03_traceSegment_045_3661_0008, g32p_row03_traceSegment_045_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3645 16 17, g32p_row03_traceSegment_045_3645_0016, g32p_row03_traceSegment_045_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3686 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3678 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3678 8 9, g32p_row03_traceSegment_045_3678_0008, g32p_row03_traceSegment_045_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3695 8 9, g32p_row03_traceSegment_045_3695_0008, g32p_row03_traceSegment_045_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3678 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3678 17 17, g32p_row03_traceSegment_045_3678_0017, g32p_row03_traceSegment_045_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 3645 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3645 33 34, g32p_row03_traceSegment_045_3645_0033, g32p_row03_traceSegment_045_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3720 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3712 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3712 8 9, g32p_row03_traceSegment_045_3712_0008, g32p_row03_traceSegment_045_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3729 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3729 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3729 8 9, g32p_row03_traceSegment_045_3729_0008, g32p_row03_traceSegment_045_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3712 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3712 17 17, g32p_row03_traceSegment_045_3712_0017, g32p_row03_traceSegment_045_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3746 8 9, g32p_row03_traceSegment_045_3746_0008, g32p_row03_traceSegment_045_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3771 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3763 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3763 8 9, g32p_row03_traceSegment_045_3763_0008, g32p_row03_traceSegment_045_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3746 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3746 17 17, g32p_row03_traceSegment_045_3746_0017, g32p_row03_traceSegment_045_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 3712 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3712 34 34, g32p_row03_traceSegment_045_3712_0034, g32p_row03_traceSegment_045_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 3645 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3645 67 68, g32p_row03_traceSegment_045_3645_0067, g32p_row03_traceSegment_045_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 3510 270 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3510 135 135, g32p_row03_traceSegment_045_3510_0135, g32p_row03_traceSegment_045_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_045 3240 540 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3240 270 270, g32p_row03_traceSegment_045_3240_0270, g32p_row03_traceSegment_045_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 3780 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3796 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3804 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3796 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3796 8 9, g32p_row03_traceSegment_045_3796_0008, g32p_row03_traceSegment_045_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 3780 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3780 16 17, g32p_row03_traceSegment_045_3780_0016, g32p_row03_traceSegment_045_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3813 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3813 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3813 8 9, g32p_row03_traceSegment_045_3813_0008, g32p_row03_traceSegment_045_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3838 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3830 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3830 8 9, g32p_row03_traceSegment_045_3830_0008, g32p_row03_traceSegment_045_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3813 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3813 17 17, g32p_row03_traceSegment_045_3813_0017, g32p_row03_traceSegment_045_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 3780 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3780 33 34, g32p_row03_traceSegment_045_3780_0033, g32p_row03_traceSegment_045_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3855 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3847 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3847 8 9, g32p_row03_traceSegment_045_3847_0008, g32p_row03_traceSegment_045_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3872 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3864 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3864 8 9, g32p_row03_traceSegment_045_3864_0008, g32p_row03_traceSegment_045_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3847 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3847 17 17, g32p_row03_traceSegment_045_3847_0017, g32p_row03_traceSegment_045_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3881 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3889 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3881 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3881 8 9, g32p_row03_traceSegment_045_3881_0008, g32p_row03_traceSegment_045_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3906 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3898 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3898 8 9, g32p_row03_traceSegment_045_3898_0008, g32p_row03_traceSegment_045_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3881 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3881 17 17, g32p_row03_traceSegment_045_3881_0017, g32p_row03_traceSegment_045_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 3847 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3847 34 34, g32p_row03_traceSegment_045_3847_0034, g32p_row03_traceSegment_045_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 3780 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3780 67 68, g32p_row03_traceSegment_045_3780_0067, g32p_row03_traceSegment_045_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3931 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3931 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3931 8 9, g32p_row03_traceSegment_045_3931_0008, g32p_row03_traceSegment_045_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 3915 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3915 16 17, g32p_row03_traceSegment_045_3915_0016, g32p_row03_traceSegment_045_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3948 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3948 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3948 8 9, g32p_row03_traceSegment_045_3948_0008, g32p_row03_traceSegment_045_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3973 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3965 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3965 8 9, g32p_row03_traceSegment_045_3965_0008, g32p_row03_traceSegment_045_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3948 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3948 17 17, g32p_row03_traceSegment_045_3948_0017, g32p_row03_traceSegment_045_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 3915 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3915 33 34, g32p_row03_traceSegment_045_3915_0033, g32p_row03_traceSegment_045_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 3990 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3982 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3982 8 9, g32p_row03_traceSegment_045_3982_0008, g32p_row03_traceSegment_045_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4007 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 3999 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3999 8 9, g32p_row03_traceSegment_045_3999_0008, g32p_row03_traceSegment_045_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 3982 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3982 17 17, g32p_row03_traceSegment_045_3982_0017, g32p_row03_traceSegment_045_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4016 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4024 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4016 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4016 8 9, g32p_row03_traceSegment_045_4016_0008, g32p_row03_traceSegment_045_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4033 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4033 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4033 8 9, g32p_row03_traceSegment_045_4033_0008, g32p_row03_traceSegment_045_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 4016 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4016 17 17, g32p_row03_traceSegment_045_4016_0017, g32p_row03_traceSegment_045_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 3982 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3982 34 34, g32p_row03_traceSegment_045_3982_0034, g32p_row03_traceSegment_045_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 3915 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3915 67 68, g32p_row03_traceSegment_045_3915_0067, g32p_row03_traceSegment_045_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 3780 270 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3780 135 135, g32p_row03_traceSegment_045_3780_0135, g32p_row03_traceSegment_045_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 4050 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4066 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4074 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4066 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4066 8 9, g32p_row03_traceSegment_045_4066_0008, g32p_row03_traceSegment_045_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 4050 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4050 16 17, g32p_row03_traceSegment_045_4050_0016, g32p_row03_traceSegment_045_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4083 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4091 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4083 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4083 8 9, g32p_row03_traceSegment_045_4083_0008, g32p_row03_traceSegment_045_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4100 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4100 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4100 8 9, g32p_row03_traceSegment_045_4100_0008, g32p_row03_traceSegment_045_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 4083 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4083 17 17, g32p_row03_traceSegment_045_4083_0017, g32p_row03_traceSegment_045_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 4050 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4050 33 34, g32p_row03_traceSegment_045_4050_0033, g32p_row03_traceSegment_045_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4117 8 9, g32p_row03_traceSegment_045_4117_0008, g32p_row03_traceSegment_045_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4134 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4142 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4134 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4134 8 9, g32p_row03_traceSegment_045_4134_0008, g32p_row03_traceSegment_045_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 4117 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4117 17 17, g32p_row03_traceSegment_045_4117_0017, g32p_row03_traceSegment_045_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4159 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4151 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4151 8 9, g32p_row03_traceSegment_045_4151_0008, g32p_row03_traceSegment_045_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4176 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4168 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4168 8 9, g32p_row03_traceSegment_045_4168_0008, g32p_row03_traceSegment_045_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 4151 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4151 17 17, g32p_row03_traceSegment_045_4151_0017, g32p_row03_traceSegment_045_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 4117 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4117 34 34, g32p_row03_traceSegment_045_4117_0034, g32p_row03_traceSegment_045_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 4050 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4050 67 68, g32p_row03_traceSegment_045_4050_0067, g32p_row03_traceSegment_045_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_045 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4201 8 9, g32p_row03_traceSegment_045_4201_0008, g32p_row03_traceSegment_045_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_045 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4185 16 17, g32p_row03_traceSegment_045_4185_0016, g32p_row03_traceSegment_045_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4218 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4218 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4218 8 9, g32p_row03_traceSegment_045_4218_0008, g32p_row03_traceSegment_045_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4235 8 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4235 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4235 8 9, g32p_row03_traceSegment_045_4235_0008, g32p_row03_traceSegment_045_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 4218 34 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4218 17 17, g32p_row03_traceSegment_045_4218_0017, g32p_row03_traceSegment_045_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_045 4185 67 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4185 33 34, g32p_row03_traceSegment_045_4185_0033, g32p_row03_traceSegment_045_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4252 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4252 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4252 8 9, g32p_row03_traceSegment_045_4252_0008, g32p_row03_traceSegment_045_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4269 8 9, g32p_row03_traceSegment_045_4269_0008, g32p_row03_traceSegment_045_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 4252 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4252 17 17, g32p_row03_traceSegment_045_4252_0017, g32p_row03_traceSegment_045_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4294 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4286 17 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4286 8 9, g32p_row03_traceSegment_045_4286_0008, g32p_row03_traceSegment_045_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_045 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_045 4311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_045_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_045 4303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4303 8 9, g32p_row03_traceSegment_045_4303_0008, g32p_row03_traceSegment_045_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_045 4286 34 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4286 17 17, g32p_row03_traceSegment_045_4286_0017, g32p_row03_traceSegment_045_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_045 4252 68 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4252 34 34, g32p_row03_traceSegment_045_4252_0034, g32p_row03_traceSegment_045_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_045 4185 135 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4185 67 68, g32p_row03_traceSegment_045_4185_0067, g32p_row03_traceSegment_045_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_045_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_045 4050 270 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 4050 135 135, g32p_row03_traceSegment_045_4050_0135, g32p_row03_traceSegment_045_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_045 3780 540 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3780 270 270, g32p_row03_traceSegment_045_3780_0270, g32p_row03_traceSegment_045_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_045_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_045 3240 1080 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 3240 540 540, g32p_row03_traceSegment_045_3240_0540, g32p_row03_traceSegment_045_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_045_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_045 2160 2160 = [0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 2160 1080 1080, g32p_row03_traceSegment_045_2160_1080, g32p_row03_traceSegment_045_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_045_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_045 0 4320 = [0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_045 0 2160 2160, g32p_row03_traceSegment_045_0000_2160, g32p_row03_traceSegment_045_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 45 = [0, 0, 40] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_045_0000_4320

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row03_traceSegment_046 (k : ℕ) : List ℤ :=
  if g32p_row03_supplierClassifier (Fin.ofNat 4320 k) = 46 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row03_characterValues (Fin.ofNat 4320 k))).val 1 else []

private theorem g32p_row03_traceSegment_046_0000_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 0 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0016_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 16 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0024_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 24 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0016_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 16 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 16 8 9, g32p_row03_traceSegment_046_0016_0008, g32p_row03_traceSegment_046_0024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0000_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 0 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 0 16 17, g32p_row03_traceSegment_046_0000_0016, g32p_row03_traceSegment_046_0016_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0033_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 33 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0041_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 41 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0033_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 33 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 33 8 9, g32p_row03_traceSegment_046_0033_0008, g32p_row03_traceSegment_046_0041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0050_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 50 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0058_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 58 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0050_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 50 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 50 8 9, g32p_row03_traceSegment_046_0050_0008, g32p_row03_traceSegment_046_0058_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0033_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 33 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 33 17 17, g32p_row03_traceSegment_046_0033_0017, g32p_row03_traceSegment_046_0050_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0000_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 0 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 0 33 34, g32p_row03_traceSegment_046_0000_0033, g32p_row03_traceSegment_046_0033_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0067_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 67 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0075_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 75 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0067_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 67 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 67 8 9, g32p_row03_traceSegment_046_0067_0008, g32p_row03_traceSegment_046_0075_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0084_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 84 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0092_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 92 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0084_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 84 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 84 8 9, g32p_row03_traceSegment_046_0084_0008, g32p_row03_traceSegment_046_0092_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0067_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 67 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 67 17 17, g32p_row03_traceSegment_046_0067_0017, g32p_row03_traceSegment_046_0084_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0101_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 101 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0109_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 109 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0101_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 101 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 101 8 9, g32p_row03_traceSegment_046_0101_0008, g32p_row03_traceSegment_046_0109_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0118_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 118 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0126_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 126 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0118_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 118 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 118 8 9, g32p_row03_traceSegment_046_0118_0008, g32p_row03_traceSegment_046_0126_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0101_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 101 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 101 17 17, g32p_row03_traceSegment_046_0101_0017, g32p_row03_traceSegment_046_0118_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0067_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 67 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 67 34 34, g32p_row03_traceSegment_046_0067_0034, g32p_row03_traceSegment_046_0101_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0000_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 0 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 0 67 68, g32p_row03_traceSegment_046_0000_0067, g32p_row03_traceSegment_046_0067_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0135_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 135 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0151_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 151 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0159_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 159 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0151_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 151 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 151 8 9, g32p_row03_traceSegment_046_0151_0008, g32p_row03_traceSegment_046_0159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0135_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 135 33 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 135 16 17, g32p_row03_traceSegment_046_0135_0016, g32p_row03_traceSegment_046_0151_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0168_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 168 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0176_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 176 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0168_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 168 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 168 8 9, g32p_row03_traceSegment_046_0168_0008, g32p_row03_traceSegment_046_0176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0185_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 185 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0193_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 193 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0185_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 185 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 185 8 9, g32p_row03_traceSegment_046_0185_0008, g32p_row03_traceSegment_046_0193_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0168_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 168 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 168 17 17, g32p_row03_traceSegment_046_0168_0017, g32p_row03_traceSegment_046_0185_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0135_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 135 67 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 135 33 34, g32p_row03_traceSegment_046_0135_0033, g32p_row03_traceSegment_046_0168_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0202_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 202 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0210_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 210 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0202_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 202 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 202 8 9, g32p_row03_traceSegment_046_0202_0008, g32p_row03_traceSegment_046_0210_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0219_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 219 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0227_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 227 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0219_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 219 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 219 8 9, g32p_row03_traceSegment_046_0219_0008, g32p_row03_traceSegment_046_0227_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0202_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 202 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 202 17 17, g32p_row03_traceSegment_046_0202_0017, g32p_row03_traceSegment_046_0219_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0236_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 236 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0244_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 244 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0236_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 236 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 236 8 9, g32p_row03_traceSegment_046_0236_0008, g32p_row03_traceSegment_046_0244_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0253_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 253 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0261_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 261 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0253_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 253 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 253 8 9, g32p_row03_traceSegment_046_0253_0008, g32p_row03_traceSegment_046_0261_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0236_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 236 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 236 17 17, g32p_row03_traceSegment_046_0236_0017, g32p_row03_traceSegment_046_0253_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0202_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 202 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 202 34 34, g32p_row03_traceSegment_046_0202_0034, g32p_row03_traceSegment_046_0236_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0135_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 135 135 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 135 67 68, g32p_row03_traceSegment_046_0135_0067, g32p_row03_traceSegment_046_0202_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0000_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 0 270 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 0 135 135, g32p_row03_traceSegment_046_0000_0135, g32p_row03_traceSegment_046_0135_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0270_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 270 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0286_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0294_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 294 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0286_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 286 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 286 8 9, g32p_row03_traceSegment_046_0286_0008, g32p_row03_traceSegment_046_0294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0270_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 270 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 270 16 17, g32p_row03_traceSegment_046_0270_0016, g32p_row03_traceSegment_046_0286_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0303_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0311_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 311 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0303_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 303 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 303 8 9, g32p_row03_traceSegment_046_0303_0008, g32p_row03_traceSegment_046_0311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0320_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 320 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0328_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 328 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0320_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 320 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 320 8 9, g32p_row03_traceSegment_046_0320_0008, g32p_row03_traceSegment_046_0328_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0303_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 303 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 303 17 17, g32p_row03_traceSegment_046_0303_0017, g32p_row03_traceSegment_046_0320_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0270_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 270 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 270 33 34, g32p_row03_traceSegment_046_0270_0033, g32p_row03_traceSegment_046_0303_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0337_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 337 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0345_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 345 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0337_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 337 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 337 8 9, g32p_row03_traceSegment_046_0337_0008, g32p_row03_traceSegment_046_0345_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0354_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 354 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0362_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 362 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0354_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 354 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 354 8 9, g32p_row03_traceSegment_046_0354_0008, g32p_row03_traceSegment_046_0362_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0337_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 337 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 337 17 17, g32p_row03_traceSegment_046_0337_0017, g32p_row03_traceSegment_046_0354_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0371_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 371 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0379_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 379 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0371_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 371 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 371 8 9, g32p_row03_traceSegment_046_0371_0008, g32p_row03_traceSegment_046_0379_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0388_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 388 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0396_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 396 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0388_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 388 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 388 8 9, g32p_row03_traceSegment_046_0388_0008, g32p_row03_traceSegment_046_0396_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0371_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 371 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 371 17 17, g32p_row03_traceSegment_046_0371_0017, g32p_row03_traceSegment_046_0388_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0337_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 337 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 337 34 34, g32p_row03_traceSegment_046_0337_0034, g32p_row03_traceSegment_046_0371_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0270_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 270 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 270 67 68, g32p_row03_traceSegment_046_0270_0067, g32p_row03_traceSegment_046_0337_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0405_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 405 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0421_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 421 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0429_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 429 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0421_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 421 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 421 8 9, g32p_row03_traceSegment_046_0421_0008, g32p_row03_traceSegment_046_0429_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0405_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 405 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 405 16 17, g32p_row03_traceSegment_046_0405_0016, g32p_row03_traceSegment_046_0421_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0438_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 438 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0446_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 446 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0438_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 438 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 438 8 9, g32p_row03_traceSegment_046_0438_0008, g32p_row03_traceSegment_046_0446_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0455_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 455 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0463_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 463 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0455_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 455 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 455 8 9, g32p_row03_traceSegment_046_0455_0008, g32p_row03_traceSegment_046_0463_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0438_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 438 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 438 17 17, g32p_row03_traceSegment_046_0438_0017, g32p_row03_traceSegment_046_0455_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0405_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 405 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 405 33 34, g32p_row03_traceSegment_046_0405_0033, g32p_row03_traceSegment_046_0438_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0472_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 472 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0480_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 480 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0472_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 472 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 472 8 9, g32p_row03_traceSegment_046_0472_0008, g32p_row03_traceSegment_046_0480_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0489_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 489 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0497_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 497 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0489_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 489 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 489 8 9, g32p_row03_traceSegment_046_0489_0008, g32p_row03_traceSegment_046_0497_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0472_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 472 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 472 17 17, g32p_row03_traceSegment_046_0472_0017, g32p_row03_traceSegment_046_0489_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0506_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 506 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0514_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 514 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0506_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 506 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 506 8 9, g32p_row03_traceSegment_046_0506_0008, g32p_row03_traceSegment_046_0514_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0523_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 523 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0531_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 531 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0523_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 523 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 523 8 9, g32p_row03_traceSegment_046_0523_0008, g32p_row03_traceSegment_046_0531_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0506_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 506 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 506 17 17, g32p_row03_traceSegment_046_0506_0017, g32p_row03_traceSegment_046_0523_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0472_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 472 68 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 472 34 34, g32p_row03_traceSegment_046_0472_0034, g32p_row03_traceSegment_046_0506_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0405_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 405 135 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 405 67 68, g32p_row03_traceSegment_046_0405_0067, g32p_row03_traceSegment_046_0472_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0270_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 270 270 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 270 135 135, g32p_row03_traceSegment_046_0270_0135, g32p_row03_traceSegment_046_0405_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0000_0540 : g32p_coeffSegment g32p_row03_traceSegment_046 0 540 = [0, 0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 0 270 270, g32p_row03_traceSegment_046_0000_0270, g32p_row03_traceSegment_046_0270_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0540_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 540 16 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0556_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 556 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0564_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 564 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0556_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 556 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 556 8 9, g32p_row03_traceSegment_046_0556_0008, g32p_row03_traceSegment_046_0564_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0540_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 540 33 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 540 16 17, g32p_row03_traceSegment_046_0540_0016, g32p_row03_traceSegment_046_0556_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0573_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 573 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0581_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 581 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0573_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 573 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 573 8 9, g32p_row03_traceSegment_046_0573_0008, g32p_row03_traceSegment_046_0581_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0590_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 590 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0598_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 598 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0590_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 590 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 590 8 9, g32p_row03_traceSegment_046_0590_0008, g32p_row03_traceSegment_046_0598_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0573_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 573 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 573 17 17, g32p_row03_traceSegment_046_0573_0017, g32p_row03_traceSegment_046_0590_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0540_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 540 67 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 540 33 34, g32p_row03_traceSegment_046_0540_0033, g32p_row03_traceSegment_046_0573_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0607_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 607 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0615_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 615 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0607_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 607 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 607 8 9, g32p_row03_traceSegment_046_0607_0008, g32p_row03_traceSegment_046_0615_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0624_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 624 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0632_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 632 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0624_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 624 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 624 8 9, g32p_row03_traceSegment_046_0624_0008, g32p_row03_traceSegment_046_0632_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0607_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 607 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 607 17 17, g32p_row03_traceSegment_046_0607_0017, g32p_row03_traceSegment_046_0624_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0641_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 641 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0649_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 649 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0641_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 641 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 641 8 9, g32p_row03_traceSegment_046_0641_0008, g32p_row03_traceSegment_046_0649_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0658_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 658 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0666_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 666 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0658_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 658 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 658 8 9, g32p_row03_traceSegment_046_0658_0008, g32p_row03_traceSegment_046_0666_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0641_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 641 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 641 17 17, g32p_row03_traceSegment_046_0641_0017, g32p_row03_traceSegment_046_0658_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0607_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 607 68 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 607 34 34, g32p_row03_traceSegment_046_0607_0034, g32p_row03_traceSegment_046_0641_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0540_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 540 135 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 540 67 68, g32p_row03_traceSegment_046_0540_0067, g32p_row03_traceSegment_046_0607_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0675_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 675 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0691_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 691 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0699_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 699 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0691_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 691 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 691 8 9, g32p_row03_traceSegment_046_0691_0008, g32p_row03_traceSegment_046_0699_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0675_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 675 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 675 16 17, g32p_row03_traceSegment_046_0675_0016, g32p_row03_traceSegment_046_0691_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0708_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 708 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0716_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 716 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0708_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 708 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 708 8 9, g32p_row03_traceSegment_046_0708_0008, g32p_row03_traceSegment_046_0716_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0725_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 725 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0733_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 733 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0725_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 725 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 725 8 9, g32p_row03_traceSegment_046_0725_0008, g32p_row03_traceSegment_046_0733_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0708_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 708 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 708 17 17, g32p_row03_traceSegment_046_0708_0017, g32p_row03_traceSegment_046_0725_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0675_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 675 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 675 33 34, g32p_row03_traceSegment_046_0675_0033, g32p_row03_traceSegment_046_0708_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0742_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 742 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0750_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 750 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0742_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 742 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 742 8 9, g32p_row03_traceSegment_046_0742_0008, g32p_row03_traceSegment_046_0750_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0759_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 759 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0767_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 767 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0759_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 759 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 759 8 9, g32p_row03_traceSegment_046_0759_0008, g32p_row03_traceSegment_046_0767_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0742_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 742 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 742 17 17, g32p_row03_traceSegment_046_0742_0017, g32p_row03_traceSegment_046_0759_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0776_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 776 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0784_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 784 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0776_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 776 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 776 8 9, g32p_row03_traceSegment_046_0776_0008, g32p_row03_traceSegment_046_0784_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0793_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 793 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0801_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 801 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0793_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 793 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 793 8 9, g32p_row03_traceSegment_046_0793_0008, g32p_row03_traceSegment_046_0801_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0776_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 776 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 776 17 17, g32p_row03_traceSegment_046_0776_0017, g32p_row03_traceSegment_046_0793_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0742_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 742 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 742 34 34, g32p_row03_traceSegment_046_0742_0034, g32p_row03_traceSegment_046_0776_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0675_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 675 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 675 67 68, g32p_row03_traceSegment_046_0675_0067, g32p_row03_traceSegment_046_0742_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0540_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 540 270 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 540 135 135, g32p_row03_traceSegment_046_0540_0135, g32p_row03_traceSegment_046_0675_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0810_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 810 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0826_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 826 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0834_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 834 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0826_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 826 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 826 8 9, g32p_row03_traceSegment_046_0826_0008, g32p_row03_traceSegment_046_0834_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0810_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 810 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 810 16 17, g32p_row03_traceSegment_046_0810_0016, g32p_row03_traceSegment_046_0826_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0843_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 843 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0851_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 851 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0843_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 843 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 843 8 9, g32p_row03_traceSegment_046_0843_0008, g32p_row03_traceSegment_046_0851_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0860_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 860 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0868_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 868 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0860_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 860 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 860 8 9, g32p_row03_traceSegment_046_0860_0008, g32p_row03_traceSegment_046_0868_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0843_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 843 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 843 17 17, g32p_row03_traceSegment_046_0843_0017, g32p_row03_traceSegment_046_0860_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0810_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 810 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 810 33 34, g32p_row03_traceSegment_046_0810_0033, g32p_row03_traceSegment_046_0843_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0877_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 877 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0885_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 885 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0877_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 877 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 877 8 9, g32p_row03_traceSegment_046_0877_0008, g32p_row03_traceSegment_046_0885_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0894_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 894 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0902_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 902 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0894_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 894 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 894 8 9, g32p_row03_traceSegment_046_0894_0008, g32p_row03_traceSegment_046_0902_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0877_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 877 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 877 17 17, g32p_row03_traceSegment_046_0877_0017, g32p_row03_traceSegment_046_0894_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0911_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 911 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0919_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 919 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0911_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 911 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 911 8 9, g32p_row03_traceSegment_046_0911_0008, g32p_row03_traceSegment_046_0919_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0928_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 928 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0936_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 936 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0928_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 928 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 928 8 9, g32p_row03_traceSegment_046_0928_0008, g32p_row03_traceSegment_046_0936_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0911_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 911 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 911 17 17, g32p_row03_traceSegment_046_0911_0017, g32p_row03_traceSegment_046_0928_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0877_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 877 68 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 877 34 34, g32p_row03_traceSegment_046_0877_0034, g32p_row03_traceSegment_046_0911_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0810_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 810 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 810 67 68, g32p_row03_traceSegment_046_0810_0067, g32p_row03_traceSegment_046_0877_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0945_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 945 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0961_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 961 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0969_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 969 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0961_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 961 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 961 8 9, g32p_row03_traceSegment_046_0961_0008, g32p_row03_traceSegment_046_0969_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0945_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 945 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 945 16 17, g32p_row03_traceSegment_046_0945_0016, g32p_row03_traceSegment_046_0961_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0978_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 978 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0986_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 986 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0978_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 978 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 978 8 9, g32p_row03_traceSegment_046_0978_0008, g32p_row03_traceSegment_046_0986_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0995_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 995 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1003_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1003 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_0995_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 995 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 995 8 9, g32p_row03_traceSegment_046_0995_0008, g32p_row03_traceSegment_046_1003_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0978_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 978 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 978 17 17, g32p_row03_traceSegment_046_0978_0017, g32p_row03_traceSegment_046_0995_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0945_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 945 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 945 33 34, g32p_row03_traceSegment_046_0945_0033, g32p_row03_traceSegment_046_0978_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1012_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1012 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1020_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1020 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1012_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1012 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1012 8 9, g32p_row03_traceSegment_046_1012_0008, g32p_row03_traceSegment_046_1020_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1029_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1029 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1037_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1037 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1029_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1029 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1029 8 9, g32p_row03_traceSegment_046_1029_0008, g32p_row03_traceSegment_046_1037_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1012_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1012 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1012 17 17, g32p_row03_traceSegment_046_1012_0017, g32p_row03_traceSegment_046_1029_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1046_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1046 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1054_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1054 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1046_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1046 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1046 8 9, g32p_row03_traceSegment_046_1046_0008, g32p_row03_traceSegment_046_1054_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1063_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1063 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1071_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1071 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1063_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1063 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1063 8 9, g32p_row03_traceSegment_046_1063_0008, g32p_row03_traceSegment_046_1071_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1046_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1046 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1046 17 17, g32p_row03_traceSegment_046_1046_0017, g32p_row03_traceSegment_046_1063_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1012_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 1012 68 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1012 34 34, g32p_row03_traceSegment_046_1012_0034, g32p_row03_traceSegment_046_1046_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0945_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 945 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 945 67 68, g32p_row03_traceSegment_046_0945_0067, g32p_row03_traceSegment_046_1012_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0810_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 810 270 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 810 135 135, g32p_row03_traceSegment_046_0810_0135, g32p_row03_traceSegment_046_0945_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0540_0540 : g32p_coeffSegment g32p_row03_traceSegment_046 540 540 = [0, 0, 0, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 540 270 270, g32p_row03_traceSegment_046_0540_0270, g32p_row03_traceSegment_046_0810_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0000_1080 : g32p_coeffSegment g32p_row03_traceSegment_046 0 1080 = [0, 0, 0, 0, 0, 33] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 0 540 540, g32p_row03_traceSegment_046_0000_0540, g32p_row03_traceSegment_046_0540_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1080_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 1080 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1096_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1096 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1104_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1104 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1096_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1096 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1096 8 9, g32p_row03_traceSegment_046_1096_0008, g32p_row03_traceSegment_046_1104_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1080_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 1080 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1080 16 17, g32p_row03_traceSegment_046_1080_0016, g32p_row03_traceSegment_046_1096_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1113_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1113 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1121_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1121 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1113_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1113 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1113 8 9, g32p_row03_traceSegment_046_1113_0008, g32p_row03_traceSegment_046_1121_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1130_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1130 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1138_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1138 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1130_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1130 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1130 8 9, g32p_row03_traceSegment_046_1130_0008, g32p_row03_traceSegment_046_1138_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1113_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1113 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1113 17 17, g32p_row03_traceSegment_046_1113_0017, g32p_row03_traceSegment_046_1130_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1080_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 1080 67 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1080 33 34, g32p_row03_traceSegment_046_1080_0033, g32p_row03_traceSegment_046_1113_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1147_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1147 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1155_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1155 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1147_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1147 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1147 8 9, g32p_row03_traceSegment_046_1147_0008, g32p_row03_traceSegment_046_1155_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1164_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1164 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1172_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1172 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1164_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1164 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1164 8 9, g32p_row03_traceSegment_046_1164_0008, g32p_row03_traceSegment_046_1172_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1147_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1147 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1147 17 17, g32p_row03_traceSegment_046_1147_0017, g32p_row03_traceSegment_046_1164_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1181_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1181 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1189_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1189 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1181_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1181 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1181 8 9, g32p_row03_traceSegment_046_1181_0008, g32p_row03_traceSegment_046_1189_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1198_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1198 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1206_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1206 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1198_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1198 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1198 8 9, g32p_row03_traceSegment_046_1198_0008, g32p_row03_traceSegment_046_1206_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1181_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1181 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1181 17 17, g32p_row03_traceSegment_046_1181_0017, g32p_row03_traceSegment_046_1198_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1147_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 1147 68 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1147 34 34, g32p_row03_traceSegment_046_1147_0034, g32p_row03_traceSegment_046_1181_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1080_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 1080 135 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1080 67 68, g32p_row03_traceSegment_046_1080_0067, g32p_row03_traceSegment_046_1147_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1215_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 1215 16 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1231_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1231 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1239_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1239 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1231_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1231 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1231 8 9, g32p_row03_traceSegment_046_1231_0008, g32p_row03_traceSegment_046_1239_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1215_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 1215 33 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1215 16 17, g32p_row03_traceSegment_046_1215_0016, g32p_row03_traceSegment_046_1231_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1248_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1248 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1256_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1256 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1248_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1248 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1248 8 9, g32p_row03_traceSegment_046_1248_0008, g32p_row03_traceSegment_046_1256_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1265_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1265 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1273_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1273 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1265_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1265 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1265 8 9, g32p_row03_traceSegment_046_1265_0008, g32p_row03_traceSegment_046_1273_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1248_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1248 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1248 17 17, g32p_row03_traceSegment_046_1248_0017, g32p_row03_traceSegment_046_1265_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1215_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 1215 67 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1215 33 34, g32p_row03_traceSegment_046_1215_0033, g32p_row03_traceSegment_046_1248_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1282_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1282 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1290_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1290 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1282_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1282 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1282 8 9, g32p_row03_traceSegment_046_1282_0008, g32p_row03_traceSegment_046_1290_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1299_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1299 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1307_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1307 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1299_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1299 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1299 8 9, g32p_row03_traceSegment_046_1299_0008, g32p_row03_traceSegment_046_1307_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1282_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1282 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1282 17 17, g32p_row03_traceSegment_046_1282_0017, g32p_row03_traceSegment_046_1299_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1316_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1316 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1324_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1324 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1316_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1316 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1316 8 9, g32p_row03_traceSegment_046_1316_0008, g32p_row03_traceSegment_046_1324_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1333_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1333 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1341_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1341 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1333_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1333 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1333 8 9, g32p_row03_traceSegment_046_1333_0008, g32p_row03_traceSegment_046_1341_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1316_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1316 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1316 17 17, g32p_row03_traceSegment_046_1316_0017, g32p_row03_traceSegment_046_1333_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1282_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 1282 68 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1282 34 34, g32p_row03_traceSegment_046_1282_0034, g32p_row03_traceSegment_046_1316_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1215_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 1215 135 = [0, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1215 67 68, g32p_row03_traceSegment_046_1215_0067, g32p_row03_traceSegment_046_1282_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1080_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 1080 270 = [0, 0, 0, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1080 135 135, g32p_row03_traceSegment_046_1080_0135, g32p_row03_traceSegment_046_1215_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1350_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 1350 16 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1366_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1366 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1374_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1374 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1366_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1366 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1366 8 9, g32p_row03_traceSegment_046_1366_0008, g32p_row03_traceSegment_046_1374_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1350_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 1350 33 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1350 16 17, g32p_row03_traceSegment_046_1350_0016, g32p_row03_traceSegment_046_1366_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1383_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1383 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1391_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1391 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1383_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1383 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1383 8 9, g32p_row03_traceSegment_046_1383_0008, g32p_row03_traceSegment_046_1391_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1400_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1400 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1408_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1408 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1400_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1400 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1400 8 9, g32p_row03_traceSegment_046_1400_0008, g32p_row03_traceSegment_046_1408_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1383_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1383 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1383 17 17, g32p_row03_traceSegment_046_1383_0017, g32p_row03_traceSegment_046_1400_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1350_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 1350 67 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1350 33 34, g32p_row03_traceSegment_046_1350_0033, g32p_row03_traceSegment_046_1383_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1417_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1417 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1425_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1425 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1417_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1417 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1417 8 9, g32p_row03_traceSegment_046_1417_0008, g32p_row03_traceSegment_046_1425_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1434_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1434 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1442_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1442 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1434_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1434 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1434 8 9, g32p_row03_traceSegment_046_1434_0008, g32p_row03_traceSegment_046_1442_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1417_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1417 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1417 17 17, g32p_row03_traceSegment_046_1417_0017, g32p_row03_traceSegment_046_1434_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1451_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1451 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1459_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1459 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1451_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1451 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1451 8 9, g32p_row03_traceSegment_046_1451_0008, g32p_row03_traceSegment_046_1459_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1468_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1468 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1476_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1476 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1468_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1468 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1468 8 9, g32p_row03_traceSegment_046_1468_0008, g32p_row03_traceSegment_046_1476_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1451_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1451 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1451 17 17, g32p_row03_traceSegment_046_1451_0017, g32p_row03_traceSegment_046_1468_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1417_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 1417 68 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1417 34 34, g32p_row03_traceSegment_046_1417_0034, g32p_row03_traceSegment_046_1451_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1350_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 1350 135 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1350 67 68, g32p_row03_traceSegment_046_1350_0067, g32p_row03_traceSegment_046_1417_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1485_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 1485 16 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1501_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1501 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1509_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1509 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1501_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1501 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1501 8 9, g32p_row03_traceSegment_046_1501_0008, g32p_row03_traceSegment_046_1509_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1485_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 1485 33 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1485 16 17, g32p_row03_traceSegment_046_1485_0016, g32p_row03_traceSegment_046_1501_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1518_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1518 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1526_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1526 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1518_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1518 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1518 8 9, g32p_row03_traceSegment_046_1518_0008, g32p_row03_traceSegment_046_1526_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1535_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1535 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1543_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1543 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1535_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1535 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1535 8 9, g32p_row03_traceSegment_046_1535_0008, g32p_row03_traceSegment_046_1543_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1518_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1518 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1518 17 17, g32p_row03_traceSegment_046_1518_0017, g32p_row03_traceSegment_046_1535_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1485_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 1485 67 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1485 33 34, g32p_row03_traceSegment_046_1485_0033, g32p_row03_traceSegment_046_1518_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1552_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1552 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1560_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1560 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1552_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1552 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1552 8 9, g32p_row03_traceSegment_046_1552_0008, g32p_row03_traceSegment_046_1560_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1569_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1569 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1577_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1577 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1569_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1569 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1569 8 9, g32p_row03_traceSegment_046_1569_0008, g32p_row03_traceSegment_046_1577_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1552_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1552 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1552 17 17, g32p_row03_traceSegment_046_1552_0017, g32p_row03_traceSegment_046_1569_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1586_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1586 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1594_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1594 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1586_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1586 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1586 8 9, g32p_row03_traceSegment_046_1586_0008, g32p_row03_traceSegment_046_1594_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1603_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1603 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1611_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1611 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1603_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1603 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1603 8 9, g32p_row03_traceSegment_046_1603_0008, g32p_row03_traceSegment_046_1611_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1586_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1586 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1586 17 17, g32p_row03_traceSegment_046_1586_0017, g32p_row03_traceSegment_046_1603_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1552_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 1552 68 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1552 34 34, g32p_row03_traceSegment_046_1552_0034, g32p_row03_traceSegment_046_1586_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1485_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 1485 135 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1485 67 68, g32p_row03_traceSegment_046_1485_0067, g32p_row03_traceSegment_046_1552_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1350_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 1350 270 = [0, 0, 0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1350 135 135, g32p_row03_traceSegment_046_1350_0135, g32p_row03_traceSegment_046_1485_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1080_0540 : g32p_coeffSegment g32p_row03_traceSegment_046 1080 540 = [0, 0, 0, 0, 0, 44] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1080 270 270, g32p_row03_traceSegment_046_1080_0270, g32p_row03_traceSegment_046_1350_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1620_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 1620 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1636_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1636 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1644_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1644 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1636_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1636 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1636 8 9, g32p_row03_traceSegment_046_1636_0008, g32p_row03_traceSegment_046_1644_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1620_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 1620 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1620 16 17, g32p_row03_traceSegment_046_1620_0016, g32p_row03_traceSegment_046_1636_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1653_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1653 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1661_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1661 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1653_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1653 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1653 8 9, g32p_row03_traceSegment_046_1653_0008, g32p_row03_traceSegment_046_1661_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1670_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1670 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1678_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1678 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1670_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1670 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1670 8 9, g32p_row03_traceSegment_046_1670_0008, g32p_row03_traceSegment_046_1678_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1653_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1653 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1653 17 17, g32p_row03_traceSegment_046_1653_0017, g32p_row03_traceSegment_046_1670_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1620_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 1620 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1620 33 34, g32p_row03_traceSegment_046_1620_0033, g32p_row03_traceSegment_046_1653_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1687_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1687 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1695_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1695 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1687_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1687 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1687 8 9, g32p_row03_traceSegment_046_1687_0008, g32p_row03_traceSegment_046_1695_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1704_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1704 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1712_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1712 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1704_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1704 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1704 8 9, g32p_row03_traceSegment_046_1704_0008, g32p_row03_traceSegment_046_1712_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1687_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1687 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1687 17 17, g32p_row03_traceSegment_046_1687_0017, g32p_row03_traceSegment_046_1704_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1721_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1721 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1729_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1729 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1721_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1721 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1721 8 9, g32p_row03_traceSegment_046_1721_0008, g32p_row03_traceSegment_046_1729_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1738_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1738 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1746_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1746 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1738_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1738 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1738 8 9, g32p_row03_traceSegment_046_1738_0008, g32p_row03_traceSegment_046_1746_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1721_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1721 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1721 17 17, g32p_row03_traceSegment_046_1721_0017, g32p_row03_traceSegment_046_1738_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1687_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 1687 68 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1687 34 34, g32p_row03_traceSegment_046_1687_0034, g32p_row03_traceSegment_046_1721_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1620_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 1620 135 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1620 67 68, g32p_row03_traceSegment_046_1620_0067, g32p_row03_traceSegment_046_1687_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1755_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 1755 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1771_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1771 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1779_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1779 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1771_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1771 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1771 8 9, g32p_row03_traceSegment_046_1771_0008, g32p_row03_traceSegment_046_1779_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1755_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 1755 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1755 16 17, g32p_row03_traceSegment_046_1755_0016, g32p_row03_traceSegment_046_1771_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1788_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1788 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1796_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1796 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1788_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1788 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1788 8 9, g32p_row03_traceSegment_046_1788_0008, g32p_row03_traceSegment_046_1796_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1805_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1805 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1813_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1813 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1805_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1805 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1805 8 9, g32p_row03_traceSegment_046_1805_0008, g32p_row03_traceSegment_046_1813_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1788_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1788 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1788 17 17, g32p_row03_traceSegment_046_1788_0017, g32p_row03_traceSegment_046_1805_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1755_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 1755 67 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1755 33 34, g32p_row03_traceSegment_046_1755_0033, g32p_row03_traceSegment_046_1788_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1822_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1822 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1830_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1830 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1822_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1822 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1822 8 9, g32p_row03_traceSegment_046_1822_0008, g32p_row03_traceSegment_046_1830_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1839_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1839 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1847_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1847 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1839_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1839 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1839 8 9, g32p_row03_traceSegment_046_1839_0008, g32p_row03_traceSegment_046_1847_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1822_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1822 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1822 17 17, g32p_row03_traceSegment_046_1822_0017, g32p_row03_traceSegment_046_1839_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1856_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1856 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1864_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1864 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1856_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1856 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1856 8 9, g32p_row03_traceSegment_046_1856_0008, g32p_row03_traceSegment_046_1864_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1873_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1873 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1881_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1881 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1873_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1873 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1873 8 9, g32p_row03_traceSegment_046_1873_0008, g32p_row03_traceSegment_046_1881_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1856_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1856 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1856 17 17, g32p_row03_traceSegment_046_1856_0017, g32p_row03_traceSegment_046_1873_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1822_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 1822 68 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1822 34 34, g32p_row03_traceSegment_046_1822_0034, g32p_row03_traceSegment_046_1856_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1755_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 1755 135 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1755 67 68, g32p_row03_traceSegment_046_1755_0067, g32p_row03_traceSegment_046_1822_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1620_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 1620 270 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1620 135 135, g32p_row03_traceSegment_046_1620_0135, g32p_row03_traceSegment_046_1755_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1890_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 1890 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1906_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1906 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1914_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1914 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1906_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1906 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1906 8 9, g32p_row03_traceSegment_046_1906_0008, g32p_row03_traceSegment_046_1914_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1890_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 1890 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1890 16 17, g32p_row03_traceSegment_046_1890_0016, g32p_row03_traceSegment_046_1906_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1923_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1923 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1931_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1931 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1923_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1923 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1923 8 9, g32p_row03_traceSegment_046_1923_0008, g32p_row03_traceSegment_046_1931_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1940_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1940 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1948_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1948 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1940_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1940 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1940 8 9, g32p_row03_traceSegment_046_1940_0008, g32p_row03_traceSegment_046_1948_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1923_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1923 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1923 17 17, g32p_row03_traceSegment_046_1923_0017, g32p_row03_traceSegment_046_1940_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1890_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 1890 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1890 33 34, g32p_row03_traceSegment_046_1890_0033, g32p_row03_traceSegment_046_1923_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1957_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1957 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1965_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1965 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1957_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1957 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1957 8 9, g32p_row03_traceSegment_046_1957_0008, g32p_row03_traceSegment_046_1965_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1974_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1974 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1982_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1982 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1974_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1974 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1974 8 9, g32p_row03_traceSegment_046_1974_0008, g32p_row03_traceSegment_046_1982_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1957_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1957 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1957 17 17, g32p_row03_traceSegment_046_1957_0017, g32p_row03_traceSegment_046_1974_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1991_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 1991 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1999_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 1999 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_1991_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 1991 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1991 8 9, g32p_row03_traceSegment_046_1991_0008, g32p_row03_traceSegment_046_1999_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2008_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2008 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2016_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2016 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2008_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2008 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2008 8 9, g32p_row03_traceSegment_046_2008_0008, g32p_row03_traceSegment_046_2016_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1991_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 1991 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1991 17 17, g32p_row03_traceSegment_046_1991_0017, g32p_row03_traceSegment_046_2008_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1957_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 1957 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1957 34 34, g32p_row03_traceSegment_046_1957_0034, g32p_row03_traceSegment_046_1991_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1890_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 1890 135 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1890 67 68, g32p_row03_traceSegment_046_1890_0067, g32p_row03_traceSegment_046_1957_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2025_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 2025 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2041_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2041 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2049_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2049 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2041_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2041 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2041 8 9, g32p_row03_traceSegment_046_2041_0008, g32p_row03_traceSegment_046_2049_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2025_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 2025 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2025 16 17, g32p_row03_traceSegment_046_2025_0016, g32p_row03_traceSegment_046_2041_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2058_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2058 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2066_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2066 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2058_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2058 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2058 8 9, g32p_row03_traceSegment_046_2058_0008, g32p_row03_traceSegment_046_2066_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2075_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2075 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2083_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2083 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2075_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2075 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2075 8 9, g32p_row03_traceSegment_046_2075_0008, g32p_row03_traceSegment_046_2083_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2058_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2058 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2058 17 17, g32p_row03_traceSegment_046_2058_0017, g32p_row03_traceSegment_046_2075_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2025_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 2025 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2025 33 34, g32p_row03_traceSegment_046_2025_0033, g32p_row03_traceSegment_046_2058_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2092_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2092 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2100_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2100 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2092_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2092 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2092 8 9, g32p_row03_traceSegment_046_2092_0008, g32p_row03_traceSegment_046_2100_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2109_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2109 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2117_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2117 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2109_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2109 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2109 8 9, g32p_row03_traceSegment_046_2109_0008, g32p_row03_traceSegment_046_2117_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2092_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2092 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2092 17 17, g32p_row03_traceSegment_046_2092_0017, g32p_row03_traceSegment_046_2109_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2126_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2126 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2134_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2134 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2126_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2126 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2126 8 9, g32p_row03_traceSegment_046_2126_0008, g32p_row03_traceSegment_046_2134_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2143_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2143 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2151_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2151 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2143_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2143 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2143 8 9, g32p_row03_traceSegment_046_2143_0008, g32p_row03_traceSegment_046_2151_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2126_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2126 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2126 17 17, g32p_row03_traceSegment_046_2126_0017, g32p_row03_traceSegment_046_2143_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2092_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 2092 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2092 34 34, g32p_row03_traceSegment_046_2092_0034, g32p_row03_traceSegment_046_2126_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2025_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 2025 135 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2025 67 68, g32p_row03_traceSegment_046_2025_0067, g32p_row03_traceSegment_046_2092_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1890_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 1890 270 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1890 135 135, g32p_row03_traceSegment_046_1890_0135, g32p_row03_traceSegment_046_2025_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1620_0540 : g32p_coeffSegment g32p_row03_traceSegment_046 1620 540 = [0, 0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1620 270 270, g32p_row03_traceSegment_046_1620_0270, g32p_row03_traceSegment_046_1890_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_046_1080_1080 : g32p_coeffSegment g32p_row03_traceSegment_046 1080 1080 = [0, 0, 0, 0, 0, 58] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 1080 540 540, g32p_row03_traceSegment_046_1080_0540, g32p_row03_traceSegment_046_1620_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0000_2160 : g32p_coeffSegment g32p_row03_traceSegment_046 0 2160 = [0, 0, 0, 0, 0, 91] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 0 1080 1080, g32p_row03_traceSegment_046_0000_1080, g32p_row03_traceSegment_046_1080_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2160_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 2160 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2176_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2176 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2184_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2184 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2176_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2176 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2176 8 9, g32p_row03_traceSegment_046_2176_0008, g32p_row03_traceSegment_046_2184_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2160_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 2160 33 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2160 16 17, g32p_row03_traceSegment_046_2160_0016, g32p_row03_traceSegment_046_2176_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2193_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2193 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2201_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2201 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2193_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2193 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2193 8 9, g32p_row03_traceSegment_046_2193_0008, g32p_row03_traceSegment_046_2201_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2210_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2210 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2218_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2218 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2210_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2210 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2210 8 9, g32p_row03_traceSegment_046_2210_0008, g32p_row03_traceSegment_046_2218_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2193_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2193 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2193 17 17, g32p_row03_traceSegment_046_2193_0017, g32p_row03_traceSegment_046_2210_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2160_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 2160 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2160 33 34, g32p_row03_traceSegment_046_2160_0033, g32p_row03_traceSegment_046_2193_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2227_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2227 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2235_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2235 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2227_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2227 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2227 8 9, g32p_row03_traceSegment_046_2227_0008, g32p_row03_traceSegment_046_2235_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2244_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2244 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2252_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2252 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2244_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2244 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2244 8 9, g32p_row03_traceSegment_046_2244_0008, g32p_row03_traceSegment_046_2252_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2227_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2227 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2227 17 17, g32p_row03_traceSegment_046_2227_0017, g32p_row03_traceSegment_046_2244_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2261_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2261 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2269_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2269 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2261_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2261 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2261 8 9, g32p_row03_traceSegment_046_2261_0008, g32p_row03_traceSegment_046_2269_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2278_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2278 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2286_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2286 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2278_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2278 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2278 8 9, g32p_row03_traceSegment_046_2278_0008, g32p_row03_traceSegment_046_2286_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2261_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2261 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2261 17 17, g32p_row03_traceSegment_046_2261_0017, g32p_row03_traceSegment_046_2278_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2227_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 2227 68 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2227 34 34, g32p_row03_traceSegment_046_2227_0034, g32p_row03_traceSegment_046_2261_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2160_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 2160 135 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2160 67 68, g32p_row03_traceSegment_046_2160_0067, g32p_row03_traceSegment_046_2227_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2295_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 2295 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2311_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2311 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2319_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2319 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2311_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2311 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2311 8 9, g32p_row03_traceSegment_046_2311_0008, g32p_row03_traceSegment_046_2319_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2295_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 2295 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2295 16 17, g32p_row03_traceSegment_046_2295_0016, g32p_row03_traceSegment_046_2311_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2328_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2328 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2336_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2336 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2328_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2328 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2328 8 9, g32p_row03_traceSegment_046_2328_0008, g32p_row03_traceSegment_046_2336_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2345_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2345 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2353_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2353 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2345_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2345 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2345 8 9, g32p_row03_traceSegment_046_2345_0008, g32p_row03_traceSegment_046_2353_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2328_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2328 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2328 17 17, g32p_row03_traceSegment_046_2328_0017, g32p_row03_traceSegment_046_2345_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2295_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 2295 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2295 33 34, g32p_row03_traceSegment_046_2295_0033, g32p_row03_traceSegment_046_2328_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2362_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2362 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2370_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2370 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2362_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2362 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2362 8 9, g32p_row03_traceSegment_046_2362_0008, g32p_row03_traceSegment_046_2370_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2379_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2379 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2387_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2387 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2379_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2379 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2379 8 9, g32p_row03_traceSegment_046_2379_0008, g32p_row03_traceSegment_046_2387_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2362_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2362 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2362 17 17, g32p_row03_traceSegment_046_2362_0017, g32p_row03_traceSegment_046_2379_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2396_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2396 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2404_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2404 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2396_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2396 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2396 8 9, g32p_row03_traceSegment_046_2396_0008, g32p_row03_traceSegment_046_2404_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2413_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2413 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2421_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2421 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2413_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2413 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2413 8 9, g32p_row03_traceSegment_046_2413_0008, g32p_row03_traceSegment_046_2421_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2396_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2396 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2396 17 17, g32p_row03_traceSegment_046_2396_0017, g32p_row03_traceSegment_046_2413_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2362_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 2362 68 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2362 34 34, g32p_row03_traceSegment_046_2362_0034, g32p_row03_traceSegment_046_2396_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2295_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 2295 135 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2295 67 68, g32p_row03_traceSegment_046_2295_0067, g32p_row03_traceSegment_046_2362_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2160_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 2160 270 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2160 135 135, g32p_row03_traceSegment_046_2160_0135, g32p_row03_traceSegment_046_2295_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2430_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 2430 16 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2446_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2446 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2454_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2454 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2446_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2446 17 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2446 8 9, g32p_row03_traceSegment_046_2446_0008, g32p_row03_traceSegment_046_2454_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2430_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 2430 33 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2430 16 17, g32p_row03_traceSegment_046_2430_0016, g32p_row03_traceSegment_046_2446_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2463_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2463 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2471_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2471 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2463_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2463 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2463 8 9, g32p_row03_traceSegment_046_2463_0008, g32p_row03_traceSegment_046_2471_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2480_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2480 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2488_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2488 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2480_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2480 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2480 8 9, g32p_row03_traceSegment_046_2480_0008, g32p_row03_traceSegment_046_2488_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2463_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2463 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2463 17 17, g32p_row03_traceSegment_046_2463_0017, g32p_row03_traceSegment_046_2480_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2430_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 2430 67 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2430 33 34, g32p_row03_traceSegment_046_2430_0033, g32p_row03_traceSegment_046_2463_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2497_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2497 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2505_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2505 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2497_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2497 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2497 8 9, g32p_row03_traceSegment_046_2497_0008, g32p_row03_traceSegment_046_2505_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2514_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2514 8 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2522_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2522 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2514_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2514 17 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2514 8 9, g32p_row03_traceSegment_046_2514_0008, g32p_row03_traceSegment_046_2522_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2497_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2497 34 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2497 17 17, g32p_row03_traceSegment_046_2497_0017, g32p_row03_traceSegment_046_2514_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2531_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2531 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2539_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2539 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2531_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2531 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2531 8 9, g32p_row03_traceSegment_046_2531_0008, g32p_row03_traceSegment_046_2539_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2548_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2548 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2556_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2556 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2548_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2548 17 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2548 8 9, g32p_row03_traceSegment_046_2548_0008, g32p_row03_traceSegment_046_2556_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2531_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2531 34 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2531 17 17, g32p_row03_traceSegment_046_2531_0017, g32p_row03_traceSegment_046_2548_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2497_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 2497 68 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2497 34 34, g32p_row03_traceSegment_046_2497_0034, g32p_row03_traceSegment_046_2531_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2430_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 2430 135 = [0, 0, 0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2430 67 68, g32p_row03_traceSegment_046_2430_0067, g32p_row03_traceSegment_046_2497_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2565_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 2565 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2581_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2581 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2589_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2589 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2581_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2581 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2581 8 9, g32p_row03_traceSegment_046_2581_0008, g32p_row03_traceSegment_046_2589_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2565_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 2565 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2565 16 17, g32p_row03_traceSegment_046_2565_0016, g32p_row03_traceSegment_046_2581_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2598_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2598 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2606_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2606 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2598_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2598 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2598 8 9, g32p_row03_traceSegment_046_2598_0008, g32p_row03_traceSegment_046_2606_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2615_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2615 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2623_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2623 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2615_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2615 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2615 8 9, g32p_row03_traceSegment_046_2615_0008, g32p_row03_traceSegment_046_2623_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2598_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2598 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2598 17 17, g32p_row03_traceSegment_046_2598_0017, g32p_row03_traceSegment_046_2615_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2565_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 2565 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2565 33 34, g32p_row03_traceSegment_046_2565_0033, g32p_row03_traceSegment_046_2598_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2632_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2632 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2640_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2640 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2632_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2632 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2632 8 9, g32p_row03_traceSegment_046_2632_0008, g32p_row03_traceSegment_046_2640_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2649_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2649 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2657_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2657 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2649_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2649 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2649 8 9, g32p_row03_traceSegment_046_2649_0008, g32p_row03_traceSegment_046_2657_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2632_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2632 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2632 17 17, g32p_row03_traceSegment_046_2632_0017, g32p_row03_traceSegment_046_2649_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2666_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2666 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2674_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2674 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2666_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2666 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2666 8 9, g32p_row03_traceSegment_046_2666_0008, g32p_row03_traceSegment_046_2674_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2683_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2683 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2691_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2691 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2683_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2683 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2683 8 9, g32p_row03_traceSegment_046_2683_0008, g32p_row03_traceSegment_046_2691_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2666_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2666 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2666 17 17, g32p_row03_traceSegment_046_2666_0017, g32p_row03_traceSegment_046_2683_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2632_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 2632 68 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2632 34 34, g32p_row03_traceSegment_046_2632_0034, g32p_row03_traceSegment_046_2666_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2565_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 2565 135 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2565 67 68, g32p_row03_traceSegment_046_2565_0067, g32p_row03_traceSegment_046_2632_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2430_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 2430 270 = [0, 0, 0, 0, 0, 25] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2430 135 135, g32p_row03_traceSegment_046_2430_0135, g32p_row03_traceSegment_046_2565_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2160_0540 : g32p_coeffSegment g32p_row03_traceSegment_046 2160 540 = [0, 0, 0, 0, 0, 37] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2160 270 270, g32p_row03_traceSegment_046_2160_0270, g32p_row03_traceSegment_046_2430_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2700_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 2700 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2716_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2716 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2724_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2724 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2716_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2716 17 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2716 8 9, g32p_row03_traceSegment_046_2716_0008, g32p_row03_traceSegment_046_2724_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2700_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 2700 33 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2700 16 17, g32p_row03_traceSegment_046_2700_0016, g32p_row03_traceSegment_046_2716_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2733_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2733 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2741_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2741 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2733_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2733 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2733 8 9, g32p_row03_traceSegment_046_2733_0008, g32p_row03_traceSegment_046_2741_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2750_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2750 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2758_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2758 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2750_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2750 17 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2750 8 9, g32p_row03_traceSegment_046_2750_0008, g32p_row03_traceSegment_046_2758_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2733_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2733 34 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2733 17 17, g32p_row03_traceSegment_046_2733_0017, g32p_row03_traceSegment_046_2750_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2700_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 2700 67 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2700 33 34, g32p_row03_traceSegment_046_2700_0033, g32p_row03_traceSegment_046_2733_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2767_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2767 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2775_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2775 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2767_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2767 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2767 8 9, g32p_row03_traceSegment_046_2767_0008, g32p_row03_traceSegment_046_2775_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2784_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2784 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2792_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2792 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2784_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2784 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2784 8 9, g32p_row03_traceSegment_046_2784_0008, g32p_row03_traceSegment_046_2792_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2767_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2767 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2767 17 17, g32p_row03_traceSegment_046_2767_0017, g32p_row03_traceSegment_046_2784_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2801_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2801 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2809_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2809 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2801_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2801 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2801 8 9, g32p_row03_traceSegment_046_2801_0008, g32p_row03_traceSegment_046_2809_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2818_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2818 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2826_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2826 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2818_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2818 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2818 8 9, g32p_row03_traceSegment_046_2818_0008, g32p_row03_traceSegment_046_2826_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2801_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2801 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2801 17 17, g32p_row03_traceSegment_046_2801_0017, g32p_row03_traceSegment_046_2818_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2767_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 2767 68 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2767 34 34, g32p_row03_traceSegment_046_2767_0034, g32p_row03_traceSegment_046_2801_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2700_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 2700 135 = [0, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2700 67 68, g32p_row03_traceSegment_046_2700_0067, g32p_row03_traceSegment_046_2767_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2835_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 2835 16 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2851_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2851 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2859_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2859 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2851_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2851 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2851 8 9, g32p_row03_traceSegment_046_2851_0008, g32p_row03_traceSegment_046_2859_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2835_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 2835 33 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2835 16 17, g32p_row03_traceSegment_046_2835_0016, g32p_row03_traceSegment_046_2851_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2868_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2868 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2876_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2876 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2868_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2868 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2868 8 9, g32p_row03_traceSegment_046_2868_0008, g32p_row03_traceSegment_046_2876_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2885_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2885 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2893_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2893 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2885_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2885 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2885 8 9, g32p_row03_traceSegment_046_2885_0008, g32p_row03_traceSegment_046_2893_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2868_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2868 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2868 17 17, g32p_row03_traceSegment_046_2868_0017, g32p_row03_traceSegment_046_2885_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2835_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 2835 67 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2835 33 34, g32p_row03_traceSegment_046_2835_0033, g32p_row03_traceSegment_046_2868_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2902_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2902 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2910_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2910 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2902_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2902 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2902 8 9, g32p_row03_traceSegment_046_2902_0008, g32p_row03_traceSegment_046_2910_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2919_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2919 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2927_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2927 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2919_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2919 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2919 8 9, g32p_row03_traceSegment_046_2919_0008, g32p_row03_traceSegment_046_2927_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2902_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2902 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2902 17 17, g32p_row03_traceSegment_046_2902_0017, g32p_row03_traceSegment_046_2919_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2936_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2936 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2944_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2944 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2936_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2936 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2936 8 9, g32p_row03_traceSegment_046_2936_0008, g32p_row03_traceSegment_046_2944_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2953_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2953 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2961_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2961 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2953_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2953 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2953 8 9, g32p_row03_traceSegment_046_2953_0008, g32p_row03_traceSegment_046_2961_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2936_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 2936 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2936 17 17, g32p_row03_traceSegment_046_2936_0017, g32p_row03_traceSegment_046_2953_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2902_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 2902 68 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2902 34 34, g32p_row03_traceSegment_046_2902_0034, g32p_row03_traceSegment_046_2936_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2835_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 2835 135 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2835 67 68, g32p_row03_traceSegment_046_2835_0067, g32p_row03_traceSegment_046_2902_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2700_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 2700 270 = [0, 0, 0, 0, 0, 29] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2700 135 135, g32p_row03_traceSegment_046_2700_0135, g32p_row03_traceSegment_046_2835_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2970_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 2970 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2986_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 2986 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2994_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 2994 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_2986_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 2986 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2986 8 9, g32p_row03_traceSegment_046_2986_0008, g32p_row03_traceSegment_046_2994_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2970_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 2970 33 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2970 16 17, g32p_row03_traceSegment_046_2970_0016, g32p_row03_traceSegment_046_2986_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3003_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3003 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3011_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3011 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3003_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3003 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3003 8 9, g32p_row03_traceSegment_046_3003_0008, g32p_row03_traceSegment_046_3011_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3020_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3020 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3028_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3028 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3020_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3020 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3020 8 9, g32p_row03_traceSegment_046_3020_0008, g32p_row03_traceSegment_046_3028_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3003_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3003 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3003 17 17, g32p_row03_traceSegment_046_3003_0017, g32p_row03_traceSegment_046_3020_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2970_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 2970 67 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2970 33 34, g32p_row03_traceSegment_046_2970_0033, g32p_row03_traceSegment_046_3003_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3037_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3037 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3045_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3045 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3037_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3037 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3037 8 9, g32p_row03_traceSegment_046_3037_0008, g32p_row03_traceSegment_046_3045_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3054_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3054 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3062_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3062 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3054_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3054 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3054 8 9, g32p_row03_traceSegment_046_3054_0008, g32p_row03_traceSegment_046_3062_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3037_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3037 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3037 17 17, g32p_row03_traceSegment_046_3037_0017, g32p_row03_traceSegment_046_3054_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3071_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3071 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3079_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3079 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3071_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3071 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3071 8 9, g32p_row03_traceSegment_046_3071_0008, g32p_row03_traceSegment_046_3079_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3088_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3088 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3096_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3096 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3088_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3088 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3088 8 9, g32p_row03_traceSegment_046_3088_0008, g32p_row03_traceSegment_046_3096_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3071_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3071 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3071 17 17, g32p_row03_traceSegment_046_3071_0017, g32p_row03_traceSegment_046_3088_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3037_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 3037 68 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3037 34 34, g32p_row03_traceSegment_046_3037_0034, g32p_row03_traceSegment_046_3071_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2970_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 2970 135 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2970 67 68, g32p_row03_traceSegment_046_2970_0067, g32p_row03_traceSegment_046_3037_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3105_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 3105 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3121_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3121 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3129_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3129 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3121_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3121 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3121 8 9, g32p_row03_traceSegment_046_3121_0008, g32p_row03_traceSegment_046_3129_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3105_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 3105 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3105 16 17, g32p_row03_traceSegment_046_3105_0016, g32p_row03_traceSegment_046_3121_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3138_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3138 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3146_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3146 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3138_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3138 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3138 8 9, g32p_row03_traceSegment_046_3138_0008, g32p_row03_traceSegment_046_3146_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3155_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3155 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3163_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3163 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3155_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3155 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3155 8 9, g32p_row03_traceSegment_046_3155_0008, g32p_row03_traceSegment_046_3163_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3138_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3138 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3138 17 17, g32p_row03_traceSegment_046_3138_0017, g32p_row03_traceSegment_046_3155_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3105_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 3105 67 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3105 33 34, g32p_row03_traceSegment_046_3105_0033, g32p_row03_traceSegment_046_3138_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3172_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3172 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3180_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3180 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3172_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3172 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3172 8 9, g32p_row03_traceSegment_046_3172_0008, g32p_row03_traceSegment_046_3180_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3189_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3189 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3197_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3197 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3189_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3189 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3189 8 9, g32p_row03_traceSegment_046_3189_0008, g32p_row03_traceSegment_046_3197_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3172_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3172 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3172 17 17, g32p_row03_traceSegment_046_3172_0017, g32p_row03_traceSegment_046_3189_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3206_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3206 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3214_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3214 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3206_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3206 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3206 8 9, g32p_row03_traceSegment_046_3206_0008, g32p_row03_traceSegment_046_3214_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3223_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3223 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3231_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3231 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3223_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3223 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3223 8 9, g32p_row03_traceSegment_046_3223_0008, g32p_row03_traceSegment_046_3231_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3206_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3206 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3206 17 17, g32p_row03_traceSegment_046_3206_0017, g32p_row03_traceSegment_046_3223_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3172_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 3172 68 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3172 34 34, g32p_row03_traceSegment_046_3172_0034, g32p_row03_traceSegment_046_3206_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3105_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 3105 135 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3105 67 68, g32p_row03_traceSegment_046_3105_0067, g32p_row03_traceSegment_046_3172_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2970_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 2970 270 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2970 135 135, g32p_row03_traceSegment_046_2970_0135, g32p_row03_traceSegment_046_3105_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2700_0540 : g32p_coeffSegment g32p_row03_traceSegment_046 2700 540 = [0, 0, 0, 0, 0, 44] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2700 270 270, g32p_row03_traceSegment_046_2700_0270, g32p_row03_traceSegment_046_2970_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2160_1080 : g32p_coeffSegment g32p_row03_traceSegment_046 2160 1080 = [0, 0, 0, 0, 0, 81] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2160 540 540, g32p_row03_traceSegment_046_2160_0540, g32p_row03_traceSegment_046_2700_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3240_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 3240 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3256_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3256 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3264_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3264 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3256_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3256 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3256 8 9, g32p_row03_traceSegment_046_3256_0008, g32p_row03_traceSegment_046_3264_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3240_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 3240 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3240 16 17, g32p_row03_traceSegment_046_3240_0016, g32p_row03_traceSegment_046_3256_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3273_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3273 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3281_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3281 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3273_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3273 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3273 8 9, g32p_row03_traceSegment_046_3273_0008, g32p_row03_traceSegment_046_3281_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3290_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3290 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3298_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3298 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3290_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3290 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3290 8 9, g32p_row03_traceSegment_046_3290_0008, g32p_row03_traceSegment_046_3298_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3273_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3273 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3273 17 17, g32p_row03_traceSegment_046_3273_0017, g32p_row03_traceSegment_046_3290_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3240_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 3240 67 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3240 33 34, g32p_row03_traceSegment_046_3240_0033, g32p_row03_traceSegment_046_3273_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3307_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3307 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3315_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3315 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3307_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3307 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3307 8 9, g32p_row03_traceSegment_046_3307_0008, g32p_row03_traceSegment_046_3315_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3324_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3324 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3332_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3332 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3324_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3324 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3324 8 9, g32p_row03_traceSegment_046_3324_0008, g32p_row03_traceSegment_046_3332_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3307_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3307 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3307 17 17, g32p_row03_traceSegment_046_3307_0017, g32p_row03_traceSegment_046_3324_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3341_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3341 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3349_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3349 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3341_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3341 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3341 8 9, g32p_row03_traceSegment_046_3341_0008, g32p_row03_traceSegment_046_3349_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3358_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3358 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3366_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3366 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3358_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3358 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3358 8 9, g32p_row03_traceSegment_046_3358_0008, g32p_row03_traceSegment_046_3366_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3341_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3341 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3341 17 17, g32p_row03_traceSegment_046_3341_0017, g32p_row03_traceSegment_046_3358_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3307_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 3307 68 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3307 34 34, g32p_row03_traceSegment_046_3307_0034, g32p_row03_traceSegment_046_3341_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3240_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 3240 135 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3240 67 68, g32p_row03_traceSegment_046_3240_0067, g32p_row03_traceSegment_046_3307_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3375_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 3375 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3391_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3391 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3399_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3399 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3391_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3391 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3391 8 9, g32p_row03_traceSegment_046_3391_0008, g32p_row03_traceSegment_046_3399_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3375_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 3375 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3375 16 17, g32p_row03_traceSegment_046_3375_0016, g32p_row03_traceSegment_046_3391_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3408_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3408 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3416_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3416 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3408_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3408 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3408 8 9, g32p_row03_traceSegment_046_3408_0008, g32p_row03_traceSegment_046_3416_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3425_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3425 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3433_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3433 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3425_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3425 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3425 8 9, g32p_row03_traceSegment_046_3425_0008, g32p_row03_traceSegment_046_3433_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3408_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3408 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3408 17 17, g32p_row03_traceSegment_046_3408_0017, g32p_row03_traceSegment_046_3425_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3375_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 3375 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3375 33 34, g32p_row03_traceSegment_046_3375_0033, g32p_row03_traceSegment_046_3408_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3442_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3442 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3450_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3450 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3442_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3442 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3442 8 9, g32p_row03_traceSegment_046_3442_0008, g32p_row03_traceSegment_046_3450_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3459_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3459 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3467_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3467 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3459_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3459 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3459 8 9, g32p_row03_traceSegment_046_3459_0008, g32p_row03_traceSegment_046_3467_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3442_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3442 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3442 17 17, g32p_row03_traceSegment_046_3442_0017, g32p_row03_traceSegment_046_3459_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3476_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3476 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3484_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3484 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3476_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3476 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3476 8 9, g32p_row03_traceSegment_046_3476_0008, g32p_row03_traceSegment_046_3484_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3493_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3493 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3501_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3501 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3493_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3493 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3493 8 9, g32p_row03_traceSegment_046_3493_0008, g32p_row03_traceSegment_046_3501_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3476_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3476 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3476 17 17, g32p_row03_traceSegment_046_3476_0017, g32p_row03_traceSegment_046_3493_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3442_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 3442 68 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3442 34 34, g32p_row03_traceSegment_046_3442_0034, g32p_row03_traceSegment_046_3476_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3375_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 3375 135 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3375 67 68, g32p_row03_traceSegment_046_3375_0067, g32p_row03_traceSegment_046_3442_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3240_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 3240 270 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3240 135 135, g32p_row03_traceSegment_046_3240_0135, g32p_row03_traceSegment_046_3375_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3510_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 3510 16 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3526_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3526 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3534_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3534 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3526_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3526 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3526 8 9, g32p_row03_traceSegment_046_3526_0008, g32p_row03_traceSegment_046_3534_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3510_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 3510 33 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3510 16 17, g32p_row03_traceSegment_046_3510_0016, g32p_row03_traceSegment_046_3526_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3543_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3543 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3551_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3551 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3543_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3543 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3543 8 9, g32p_row03_traceSegment_046_3543_0008, g32p_row03_traceSegment_046_3551_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3560_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3560 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3568_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3568 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3560_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3560 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3560 8 9, g32p_row03_traceSegment_046_3560_0008, g32p_row03_traceSegment_046_3568_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3543_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3543 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3543 17 17, g32p_row03_traceSegment_046_3543_0017, g32p_row03_traceSegment_046_3560_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3510_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 3510 67 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3510 33 34, g32p_row03_traceSegment_046_3510_0033, g32p_row03_traceSegment_046_3543_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3577_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3577 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3585_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3585 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3577_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3577 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3577 8 9, g32p_row03_traceSegment_046_3577_0008, g32p_row03_traceSegment_046_3585_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3594_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3594 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3602_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3602 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3594_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3594 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3594 8 9, g32p_row03_traceSegment_046_3594_0008, g32p_row03_traceSegment_046_3602_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3577_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3577 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3577 17 17, g32p_row03_traceSegment_046_3577_0017, g32p_row03_traceSegment_046_3594_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3611_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3611 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3619_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3619 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3611_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3611 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3611 8 9, g32p_row03_traceSegment_046_3611_0008, g32p_row03_traceSegment_046_3619_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3628_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3628 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3636_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3636 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3628_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3628 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3628 8 9, g32p_row03_traceSegment_046_3628_0008, g32p_row03_traceSegment_046_3636_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3611_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3611 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3611 17 17, g32p_row03_traceSegment_046_3611_0017, g32p_row03_traceSegment_046_3628_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3577_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 3577 68 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3577 34 34, g32p_row03_traceSegment_046_3577_0034, g32p_row03_traceSegment_046_3611_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3510_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 3510 135 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3510 67 68, g32p_row03_traceSegment_046_3510_0067, g32p_row03_traceSegment_046_3577_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3645_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 3645 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3661_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3661 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3669_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3669 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3661_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3661 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3661 8 9, g32p_row03_traceSegment_046_3661_0008, g32p_row03_traceSegment_046_3669_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3645_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 3645 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3645 16 17, g32p_row03_traceSegment_046_3645_0016, g32p_row03_traceSegment_046_3661_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3678_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3678 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3686_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3686 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3678_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3678 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3678 8 9, g32p_row03_traceSegment_046_3678_0008, g32p_row03_traceSegment_046_3686_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3695_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3695 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3703_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3703 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3695_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3695 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3695 8 9, g32p_row03_traceSegment_046_3695_0008, g32p_row03_traceSegment_046_3703_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3678_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3678 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3678 17 17, g32p_row03_traceSegment_046_3678_0017, g32p_row03_traceSegment_046_3695_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3645_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 3645 67 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3645 33 34, g32p_row03_traceSegment_046_3645_0033, g32p_row03_traceSegment_046_3678_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3712_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3712 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3720_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3720 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3712_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3712 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3712 8 9, g32p_row03_traceSegment_046_3712_0008, g32p_row03_traceSegment_046_3720_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3729_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3729 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3737_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3737 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3729_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3729 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3729 8 9, g32p_row03_traceSegment_046_3729_0008, g32p_row03_traceSegment_046_3737_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3712_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3712 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3712 17 17, g32p_row03_traceSegment_046_3712_0017, g32p_row03_traceSegment_046_3729_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3746_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3746 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3754_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3754 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3746_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3746 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3746 8 9, g32p_row03_traceSegment_046_3746_0008, g32p_row03_traceSegment_046_3754_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3763_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3763 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3771_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3771 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3763_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3763 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3763 8 9, g32p_row03_traceSegment_046_3763_0008, g32p_row03_traceSegment_046_3771_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3746_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3746 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3746 17 17, g32p_row03_traceSegment_046_3746_0017, g32p_row03_traceSegment_046_3763_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3712_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 3712 68 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3712 34 34, g32p_row03_traceSegment_046_3712_0034, g32p_row03_traceSegment_046_3746_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3645_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 3645 135 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3645 67 68, g32p_row03_traceSegment_046_3645_0067, g32p_row03_traceSegment_046_3712_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3510_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 3510 270 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3510 135 135, g32p_row03_traceSegment_046_3510_0135, g32p_row03_traceSegment_046_3645_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3240_0540 : g32p_coeffSegment g32p_row03_traceSegment_046 3240 540 = [0, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3240 270 270, g32p_row03_traceSegment_046_3240_0270, g32p_row03_traceSegment_046_3510_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3780_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 3780 16 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3796_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3796 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3804_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3804 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3796_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3796 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3796 8 9, g32p_row03_traceSegment_046_3796_0008, g32p_row03_traceSegment_046_3804_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3780_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 3780 33 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3780 16 17, g32p_row03_traceSegment_046_3780_0016, g32p_row03_traceSegment_046_3796_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3813_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3813 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3821_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3821 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3813_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3813 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3813 8 9, g32p_row03_traceSegment_046_3813_0008, g32p_row03_traceSegment_046_3821_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3830_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3830 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3838_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3838 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3830_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3830 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3830 8 9, g32p_row03_traceSegment_046_3830_0008, g32p_row03_traceSegment_046_3838_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3813_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3813 34 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3813 17 17, g32p_row03_traceSegment_046_3813_0017, g32p_row03_traceSegment_046_3830_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3780_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 3780 67 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3780 33 34, g32p_row03_traceSegment_046_3780_0033, g32p_row03_traceSegment_046_3813_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3847_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3847 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3855_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3855 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3847_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3847 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3847 8 9, g32p_row03_traceSegment_046_3847_0008, g32p_row03_traceSegment_046_3855_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3864_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3864 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3872_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3872 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3864_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3864 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3864 8 9, g32p_row03_traceSegment_046_3864_0008, g32p_row03_traceSegment_046_3872_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3847_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3847 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3847 17 17, g32p_row03_traceSegment_046_3847_0017, g32p_row03_traceSegment_046_3864_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3881_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3881 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3889_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3889 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3881_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3881 17 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3881 8 9, g32p_row03_traceSegment_046_3881_0008, g32p_row03_traceSegment_046_3889_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3898_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3898 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3906_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3906 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3898_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3898 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3898 8 9, g32p_row03_traceSegment_046_3898_0008, g32p_row03_traceSegment_046_3906_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3881_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3881 34 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3881 17 17, g32p_row03_traceSegment_046_3881_0017, g32p_row03_traceSegment_046_3898_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3847_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 3847 68 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3847 34 34, g32p_row03_traceSegment_046_3847_0034, g32p_row03_traceSegment_046_3881_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3780_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 3780 135 = [0, 0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3780 67 68, g32p_row03_traceSegment_046_3780_0067, g32p_row03_traceSegment_046_3847_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3915_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 3915 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3931_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3931 8 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3939_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3939 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3931_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3931 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3931 8 9, g32p_row03_traceSegment_046_3931_0008, g32p_row03_traceSegment_046_3939_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3915_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 3915 33 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3915 16 17, g32p_row03_traceSegment_046_3915_0016, g32p_row03_traceSegment_046_3931_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3948_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3948 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3956_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3956 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3948_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3948 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3948 8 9, g32p_row03_traceSegment_046_3948_0008, g32p_row03_traceSegment_046_3956_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3965_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3965 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3973_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3973 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3965_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3965 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3965 8 9, g32p_row03_traceSegment_046_3965_0008, g32p_row03_traceSegment_046_3973_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3948_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3948 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3948 17 17, g32p_row03_traceSegment_046_3948_0017, g32p_row03_traceSegment_046_3965_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3915_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 3915 67 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3915 33 34, g32p_row03_traceSegment_046_3915_0033, g32p_row03_traceSegment_046_3948_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3982_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3982 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3990_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 3990 9 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3982_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3982 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3982 8 9, g32p_row03_traceSegment_046_3982_0008, g32p_row03_traceSegment_046_3990_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3999_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 3999 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4007_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4007 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_3999_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 3999 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3999 8 9, g32p_row03_traceSegment_046_3999_0008, g32p_row03_traceSegment_046_4007_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3982_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 3982 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3982 17 17, g32p_row03_traceSegment_046_3982_0017, g32p_row03_traceSegment_046_3999_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4016_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4016 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4024_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4024 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4016_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4016 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4016 8 9, g32p_row03_traceSegment_046_4016_0008, g32p_row03_traceSegment_046_4024_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4033_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4033 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4041_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4041 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4033_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4033 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4033 8 9, g32p_row03_traceSegment_046_4033_0008, g32p_row03_traceSegment_046_4041_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4016_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 4016 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4016 17 17, g32p_row03_traceSegment_046_4016_0017, g32p_row03_traceSegment_046_4033_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3982_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 3982 68 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3982 34 34, g32p_row03_traceSegment_046_3982_0034, g32p_row03_traceSegment_046_4016_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3915_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 3915 135 = [0, 0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3915 67 68, g32p_row03_traceSegment_046_3915_0067, g32p_row03_traceSegment_046_3982_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3780_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 3780 270 = [0, 0, 0, 0, 0, 28] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3780 135 135, g32p_row03_traceSegment_046_3780_0135, g32p_row03_traceSegment_046_3915_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4050_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 4050 16 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4066_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4066 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4074_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4074 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4066_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4066 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4066 8 9, g32p_row03_traceSegment_046_4066_0008, g32p_row03_traceSegment_046_4074_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4050_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 4050 33 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4050 16 17, g32p_row03_traceSegment_046_4050_0016, g32p_row03_traceSegment_046_4066_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4083_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4083 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4091_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4091 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4083_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4083 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4083 8 9, g32p_row03_traceSegment_046_4083_0008, g32p_row03_traceSegment_046_4091_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4100_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4100 8 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4108_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4108 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4100_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4100 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4100 8 9, g32p_row03_traceSegment_046_4100_0008, g32p_row03_traceSegment_046_4108_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4083_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 4083 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4083 17 17, g32p_row03_traceSegment_046_4083_0017, g32p_row03_traceSegment_046_4100_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4050_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 4050 67 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4050 33 34, g32p_row03_traceSegment_046_4050_0033, g32p_row03_traceSegment_046_4083_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4117_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4117 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4125_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4125 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4117_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4117 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4117 8 9, g32p_row03_traceSegment_046_4117_0008, g32p_row03_traceSegment_046_4125_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4134_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4134 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4142_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4142 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4134_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4134 17 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4134 8 9, g32p_row03_traceSegment_046_4134_0008, g32p_row03_traceSegment_046_4142_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4117_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 4117 34 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4117 17 17, g32p_row03_traceSegment_046_4117_0017, g32p_row03_traceSegment_046_4134_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4151_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4151 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4159_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4159 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4151_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4151 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4151 8 9, g32p_row03_traceSegment_046_4151_0008, g32p_row03_traceSegment_046_4159_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4168_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4168 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4176_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4176 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4168_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4168 17 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4168 8 9, g32p_row03_traceSegment_046_4168_0008, g32p_row03_traceSegment_046_4176_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4151_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 4151 34 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4151 17 17, g32p_row03_traceSegment_046_4151_0017, g32p_row03_traceSegment_046_4168_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4117_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 4117 68 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4117 34 34, g32p_row03_traceSegment_046_4117_0034, g32p_row03_traceSegment_046_4151_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4050_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 4050 135 = [0, 0, 0, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4050 67 68, g32p_row03_traceSegment_046_4050_0067, g32p_row03_traceSegment_046_4117_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4185_0016 : g32p_coeffSegment g32p_row03_traceSegment_046 4185 16 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4201_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4201 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4209_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4209 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4201_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4201 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4201 8 9, g32p_row03_traceSegment_046_4201_0008, g32p_row03_traceSegment_046_4209_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4185_0033 : g32p_coeffSegment g32p_row03_traceSegment_046 4185 33 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4185 16 17, g32p_row03_traceSegment_046_4185_0016, g32p_row03_traceSegment_046_4201_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4218_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4218 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4226_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4226 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4218_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4218 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4218 8 9, g32p_row03_traceSegment_046_4218_0008, g32p_row03_traceSegment_046_4226_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4235_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4235 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4243_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4243 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4235_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4235 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4235 8 9, g32p_row03_traceSegment_046_4235_0008, g32p_row03_traceSegment_046_4243_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4218_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 4218 34 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4218 17 17, g32p_row03_traceSegment_046_4218_0017, g32p_row03_traceSegment_046_4235_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4185_0067 : g32p_coeffSegment g32p_row03_traceSegment_046 4185 67 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4185 33 34, g32p_row03_traceSegment_046_4185_0033, g32p_row03_traceSegment_046_4218_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4252_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4252 8 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4260_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4260 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4252_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4252 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4252 8 9, g32p_row03_traceSegment_046_4252_0008, g32p_row03_traceSegment_046_4260_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4269_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4269 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4277_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4277 9 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4269_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4269 17 = [] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4269 8 9, g32p_row03_traceSegment_046_4269_0008, g32p_row03_traceSegment_046_4277_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4252_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 4252 34 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4252 17 17, g32p_row03_traceSegment_046_4252_0017, g32p_row03_traceSegment_046_4269_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4286_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4286 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4294_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4294 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4286_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4286 17 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4286 8 9, g32p_row03_traceSegment_046_4286_0008, g32p_row03_traceSegment_046_4294_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4303_0008 : g32p_coeffSegment g32p_row03_traceSegment_046 4303 8 = [] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4311_0009 : g32p_coeffSegment g32p_row03_traceSegment_046 4311 9 = [0, 0, 0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row03_traceSegment_046_4303_0017 : g32p_coeffSegment g32p_row03_traceSegment_046 4303 17 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4303 8 9, g32p_row03_traceSegment_046_4303_0008, g32p_row03_traceSegment_046_4311_0009]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4286_0034 : g32p_coeffSegment g32p_row03_traceSegment_046 4286 34 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4286 17 17, g32p_row03_traceSegment_046_4286_0017, g32p_row03_traceSegment_046_4303_0017]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4252_0068 : g32p_coeffSegment g32p_row03_traceSegment_046 4252 68 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4252 34 34, g32p_row03_traceSegment_046_4252_0034, g32p_row03_traceSegment_046_4286_0034]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4185_0135 : g32p_coeffSegment g32p_row03_traceSegment_046 4185 135 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4185 67 68, g32p_row03_traceSegment_046_4185_0067, g32p_row03_traceSegment_046_4252_0068]
  decide +kernel

private theorem g32p_row03_traceSegment_046_4050_0270 : g32p_coeffSegment g32p_row03_traceSegment_046 4050 270 = [0, 0, 0, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 4050 135 135, g32p_row03_traceSegment_046_4050_0135, g32p_row03_traceSegment_046_4185_0135]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3780_0540 : g32p_coeffSegment g32p_row03_traceSegment_046 3780 540 = [0, 0, 0, 0, 0, 52] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3780 270 270, g32p_row03_traceSegment_046_3780_0270, g32p_row03_traceSegment_046_4050_0270]
  decide +kernel

private theorem g32p_row03_traceSegment_046_3240_1080 : g32p_coeffSegment g32p_row03_traceSegment_046 3240 1080 = [0, 0, 0, 0, 0, 68] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 3240 540 540, g32p_row03_traceSegment_046_3240_0540, g32p_row03_traceSegment_046_3780_0540]
  decide +kernel

private theorem g32p_row03_traceSegment_046_2160_2160 : g32p_coeffSegment g32p_row03_traceSegment_046 2160 2160 = [0, 0, 0, 0, 0, 149] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 2160 1080 1080, g32p_row03_traceSegment_046_2160_1080, g32p_row03_traceSegment_046_3240_1080]
  decide +kernel

private theorem g32p_row03_traceSegment_046_0000_4320 : g32p_coeffSegment g32p_row03_traceSegment_046 0 4320 = [0, 0, 0, 0, 0, 240] := by
  rw [g32p_coeffSegment_add g32p_row03_traceSegment_046 0 2160 2160, g32p_row03_traceSegment_046_0000_2160, g32p_row03_traceSegment_046_2160_2160]
  decide +kernel

theorem g32p_row03_traceCoefficients_046 :
    g32p_supplierTraceCoefficients g32p_row03_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row03_characterValues j)).val) 46 = [0, 0, 0, 0, 0, 240] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row03_traceSegment_046_0000_4320

end HodgeLean.Foundations.Program

end
end
